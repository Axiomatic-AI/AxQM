/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import AxQM.ToMathlib.Analysis.InnerProductSpace.LiebConcavityTrace
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Quantum relative entropy

For density operators `ρ, σ : E →L[𝕜] E` on a finite-dimensional inner product space, the
**(Umegaki) quantum relative entropy** of `ρ` with respect to `σ` is
`D(ρ ‖ σ) = re tr(ρ log ρ) - re tr(ρ log σ)`.

## Main definitions

- `ContinuousLinearMap.quantumRelativeEntropy : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ`
-/

@[expose] public section

open scoped Topology
open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [CompleteSpace E]
    [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- The **(Umegaki) quantum relative entropy** of `ρ` with respect to `σ`: `D(ρ ‖ σ) := re tr(ρ log
ρ) - re tr(ρ log σ)`, where the operator logarithm is taken via the continuous functional
calculus. Junk-valued (still parses but carries no quantum-information meaning) when the
arguments are not density operators or `σ` has a zero eigenvalue. -/
noncomputable def quantumRelativeEntropy (ρ σ : E →L[𝕜] E) : ℝ :=
  RCLike.re (LinearMap.trace 𝕜 E ((cfc Real.log ρ).toLinearMap ∘ₗ ρ.toLinearMap)) -
    RCLike.re (LinearMap.trace 𝕜 E ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap))

end RCLike

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Trace of tensor-product composition factors** (CLM, ℂ-finite-dim): for any `A, C : E →L[ℂ] E`
and `B, D : F →L[ℂ] F`, `tr((mapL A B) ∘ (mapL C D)) = tr(A ∘ C) * tr(B ∘ D)`. -/
theorem trace_mapL_comp_mapL
    (A C : E →L[ℂ] E) (B D : F →L[ℂ] F) :
    LinearMap.trace ℂ (E ⊗[ℂ] F)
        ((TensorProduct.mapL A B).toLinearMap ∘ₗ (TensorProduct.mapL C D).toLinearMap) =
      LinearMap.trace ℂ E (A.toLinearMap ∘ₗ C.toLinearMap) *
        LinearMap.trace ℂ F (B.toLinearMap ∘ₗ D.toLinearMap) := by
  rw [TensorProduct.mapL_toLinearMap, TensorProduct.mapL_toLinearMap,
    ← TensorProduct.map_comp, LinearMap.trace_tensorProduct']

/-- **A tensor product of density operators is a density operator.** -/
theorem IsDensityOp.mapL {ρ₁ : E →L[ℂ] E} {ρ₂ : F →L[ℂ] F}
    (hρ₁ : ρ₁.IsDensityOp) (hρ₂ : ρ₂.IsDensityOp) : (TensorProduct.mapL ρ₁ ρ₂).IsDensityOp := by
  refine ⟨(nonneg_iff_isPositive _).mp (TensorProduct.mapL_nonneg hρ₁.nonneg hρ₂.nonneg), ?_⟩
  rw [TensorProduct.mapL_toLinearMap, LinearMap.trace_tensorProduct', hρ₁.trace_eq_one,
    hρ₂.trace_eq_one, mul_one]

end Complex

section GeneralOperatorFacts

open scoped ComplexOrder

/-- **Trace of a tensor-product operator factorises:** `tr (A ⊗ B) = (tr A) · (tr B)`. -/
theorem trace_mapL {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    LinearMap.trace ℂ (TensorProduct ℂ E F) ↑(TensorProduct.mapL A B) =
      LinearMap.trace ℂ E ↑A * LinearMap.trace ℂ F ↑B := by
  have h := trace_mapL_comp_mapL A 1 B 1
  simpa only [TensorProduct.mapL_one, ContinuousLinearMap.coe_one, LinearMap.comp_id] using h

/-- **`mapL A B` is an involution when `A`, `B` are:** `(A ⊗ B)² = 1` from `A² = 1` and
`B² = 1`. -/
theorem mapL_mul_mapL_self {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : A * A = 1) (hB : B * B = 1) :
    TensorProduct.mapL A B * TensorProduct.mapL A B = 1 := by
  rw [← TensorProduct.mapL_mul, hA, hB, TensorProduct.mapL_one]

/-- **`I − cG` is positive for a self-adjoint involution `G` and `c² ≤ 1`.** -/
theorem isPositive_one_sub_smul_of_selfAdjoint_involution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {G : E →L[ℂ] E} (hsa : IsSelfAdjoint G)
    (hG : G * G = 1) {c : ℝ} (hc : c ^ 2 ≤ 1) : (1 - (c : ℂ) • G).IsPositive := by
  have h1sa : IsSelfAdjoint (1 : E →L[ℂ] E) := by rw [isSelfAdjoint_iff, star_one]
  have hhalf : IsSelfAdjoint ((2 : ℂ)⁻¹) := by rw [isSelfAdjoint_iff]; simp
  have hPsa : IsSelfAdjoint ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) + G)) := by
    rw [isSelfAdjoint_iff, star_smul, hhalf.star_eq, star_add, h1sa.star_eq, hsa.star_eq]
  have hQsa : IsSelfAdjoint ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) - G)) := by
    rw [isSelfAdjoint_iff, star_smul, hhalf.star_eq, star_sub, h1sa.star_eq, hsa.star_eq]
  have hPidem : IsIdempotentElem ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) + G)) := by
    have h2 : ((1 : E →L[ℂ] E) + G) * (1 + G) = (2 : ℂ) • (1 + G) := by
      rw [add_mul, mul_add, mul_add, mul_one, one_mul, mul_one, hG]; module
    unfold IsIdempotentElem
    rw [smul_mul_smul_comm, h2, smul_smul]; norm_num
  have hQidem : IsIdempotentElem ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) - G)) := by
    have h2 : ((1 : E →L[ℂ] E) - G) * (1 - G) = (2 : ℂ) • (1 - G) := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one, hG]; module
    unfold IsIdempotentElem
    rw [smul_mul_smul_comm, h2, smul_smul]; norm_num
  have hP := (IsIdempotentElem.isPositive_iff_isSelfAdjoint hPidem).mpr hPsa
  have hQ := (IsIdempotentElem.isPositive_iff_isSelfAdjoint hQidem).mpr hQsa
  have hdecomp : (1 : E →L[ℂ] E) - (c : ℂ) • G
      = ((1 - c : ℝ) : ℂ) • ((2 : ℂ)⁻¹ • (1 + G)) + ((1 + c : ℝ) : ℂ) • ((2 : ℂ)⁻¹ • (1 - G)) := by
    push_cast; module
  rw [hdecomp]
  have h1c : (0 : ℝ) ≤ 1 - c := by nlinarith [hc, sq_nonneg (1 - c), sq_nonneg (1 + c)]
  have h1c' : (0 : ℝ) ≤ 1 + c := by nlinarith [hc, sq_nonneg (1 - c), sq_nonneg (1 + c)]
  exact (hP.smul_of_nonneg (Complex.zero_le_real.mpr h1c)).add
    (hQ.smul_of_nonneg (Complex.zero_le_real.mpr h1c'))

end GeneralOperatorFacts

end ContinuousLinearMap
