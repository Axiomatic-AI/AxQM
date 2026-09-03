/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import AxQM.ToMathlib.Analysis.InnerProductSpace.CFC
public import AxQM.ToMathlib.Analysis.InnerProductSpace.HSPairing
public import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Positive
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Trace

/-!

# Density operators

A **density operator** on a finite-dimensional inner product space `E` is a positive
continuous linear operator `T : E →L[𝕜] E` whose trace equals one. Density operators
form a convex set.

## Main definitions

* `ContinuousLinearMap.IsDensityOp T`: `T.IsPositive ∧ trace T = 1`.

## Main results

* `IsDensityOp.isPositive`, `IsDensityOp.nonneg`, `IsDensityOp.isSymmetric`,
  `IsDensityOp.trace_eq_one`: unpacking lemmas.
* `IsDensityOp.isStrictlyPositive`: a full-rank (`IsUnit`) density operator is strictly positive.
* `IsDensityOp.eigenvalues_nonneg`: the eigenvalues of a density operator are non-negative.
* `IsDensityOp.eigenvalues_sum_eq_one`: the eigenvalues sum to 1.
* `IsDensityOp.eigenvalues_le_one`: each eigenvalue is at most 1.
* `IsDensityOp.convex_combination`: the set of density operators is convex.
* `cfc_sqrt_adjoint_comp_comp_cfc_sqrt_comp_eq`: bilinear sqrt-sandwich
  `(√x Y)† (√x Z) = Y† x Z`.
* `trace_cfc_sqrt_sandwich_eq_trace_mul`: `tr(√x · S · √x) = tr(S · x)` for `0 ≤ x`.
* `re_hsPairing_cfc_sqrt_self_eq_re_trace_of_nonneg`: HS-norm² of `√x` equals
  `re tr x` for `0 ≤ x`.
* `IsDensityOp.re_hsPairing_cfc_sqrt_self_eq_one`: trace-1 specialization;
  `re hsPairing (√ρ) (√ρ) = 1` for density `ρ`.
-/

@[expose] public section

open Module
open scoped ComplexOrder InnerProductSpace

namespace ContinuousLinearMap

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A **density operator** is a positive continuous linear operator with trace 1. -/
def IsDensityOp (T : E →L[𝕜] E) : Prop :=
  T.IsPositive ∧ LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) = 1

omit [FiniteDimensional 𝕜 E] in
/-- Logical form of `IsDensityOp`: positivity and unit trace, as an `Iff`. -/
theorem isDensityOp_iff {T : E →L[𝕜] E} :
    T.IsDensityOp ↔ T.IsPositive ∧ LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) = 1 := Iff.rfl

end

namespace IsDensityOp

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {T S : E →L[𝕜] E}

protected theorem isPositive (h : T.IsDensityOp) : T.IsPositive := h.1

protected theorem nonneg (h : T.IsDensityOp) : 0 ≤ T :=
  (ContinuousLinearMap.nonneg_iff_isPositive T).mpr h.isPositive

/-- A density operator that is invertible (full-rank) is strictly positive. -/
protected theorem isStrictlyPositive (h : T.IsDensityOp) (hu : IsUnit T) : IsStrictlyPositive T :=
  ⟨h.nonneg, hu⟩

protected theorem trace_eq_one (h : T.IsDensityOp) :
    LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) = 1 := h.2

protected theorem isSymmetric (h : T.IsDensityOp) : (T : E →ₗ[𝕜] E).IsSymmetric :=
  h.isPositive.isSymmetric

/-- The set of density operators is convex: a convex combination of density operators
is itself a density operator. -/
theorem convex_combination (hT : T.IsDensityOp) (hS : S.IsDensityOp)
    {t s : 𝕜} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    (t • T + s • S).IsDensityOp := by
  refine ⟨(hT.isPositive.smul_of_nonneg ht).add (hS.isPositive.smul_of_nonneg hs), ?_⟩
  rw [coe_add, coe_smul, coe_smul, map_add, map_smul, map_smul,
    hT.trace_eq_one, hS.trace_eq_one, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hts]

/-- **Transport for density operators.** The `IsDensityOp` property is invariant under
conjugation by a linear isometry equivalence. -/
@[simp]
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_isDensityOp_iff [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [CompleteSpace F] (e : E ≃ₗᵢ[𝕜] F) :
    (e.conjStarAlgEquiv T).IsDensityOp ↔ T.IsDensityOp := by
  rw [ContinuousLinearMap.isDensityOp_iff, ContinuousLinearMap.isDensityOp_iff,
    LinearIsometryEquiv.conjStarAlgEquiv_isPositive_iff,
    ContinuousLinearMap.trace_conjStarAlgEquiv]

/-- **Density operators are preserved by conjugation by a (possibly non-surjective) isometry.** For
`V : E →L[𝕜] F` with `V† V = 1`, `V T V†` is a density operator whenever `T` is. -/
theorem conj_isometry [FiniteDimensional 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F] {V : E →L[𝕜] F}
    (hV : V.adjoint ∘L V = 1) (h : T.IsDensityOp) :
    (V ∘L T ∘L V.adjoint).IsDensityOp :=
  ⟨h.isPositive.conj_adjoint V, by
    rw [ContinuousLinearMap.trace_conj_isometry hV, h.trace_eq_one]⟩

end

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {T : E →L[𝕜] E}

/-- The eigenvalues of a density operator are non-negative. -/
theorem eigenvalues_nonneg (h : T.IsDensityOp) {n : ℕ} (hn : finrank 𝕜 E = n)
    (i : Fin n) : 0 ≤ h.isSymmetric.eigenvalues hn i :=
  h.isPositive.toLinearMap.nonneg_eigenvalues hn i

/-- The eigenvalues of a density operator sum to 1. -/
theorem eigenvalues_sum_eq_one (h : T.IsDensityOp) {n : ℕ} (hn : finrank 𝕜 E = n) :
    ∑ i, h.isSymmetric.eigenvalues hn i = 1 := by
  have := h.isSymmetric.re_trace_eq_sum_eigenvalues hn
  rw [← this, h.trace_eq_one, RCLike.one_re]

/-- Each eigenvalue of a density operator is at most 1. -/
theorem eigenvalues_le_one (h : T.IsDensityOp) {n : ℕ} (hn : finrank 𝕜 E = n)
    (i : Fin n) : h.isSymmetric.eigenvalues hn i ≤ 1 :=
  (Finset.single_le_sum (fun j _ ↦ h.eigenvalues_nonneg hn j) (Finset.mem_univ i)).trans
    (h.eigenvalues_sum_eq_one hn).le

end

end IsDensityOp

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A normalized rank-one self-projector `rankOne 𝕜 v v` is a density operator. -/
theorem isDensityOp_rankOne_self {v : E} (hv : ‖v‖ = 1) :
    (InnerProductSpace.rankOne 𝕜 v v).IsDensityOp := by
  refine ⟨InnerProductSpace.isPositive_rankOne_self v, ?_⟩
  rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, hv]
  simp

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **A strictly positive operator is positive-definite.** For `ρ` strictly positive (positive and
invertible) and `z ≠ 0`, the quadratic form `re ⟪ρ z, z⟫` is strictly positive. -/
theorem _root_.IsStrictlyPositive.re_inner_self_pos {ρ : E →L[ℂ] E} (hρ : IsStrictlyPositive ρ)
    {z : E} (hz : z ≠ 0) : 0 < RCLike.re (⟪ρ z, z⟫_ℂ) := by
  obtain ⟨hsqrtU, hρeq⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt).mp hρ
  have hRz : CFC.sqrt ρ z ≠ 0 :=
    fun h ↦ hz ((ContinuousLinearMap.isUnit_iff_bijective.mp hsqrtU).1 (by rw [h, map_zero]))
  rw [hρeq, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_right,
    (CFC.sqrt_nonneg ρ).isSelfAdjoint.adjoint_eq, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact pow_pos (norm_pos_iff.mpr hRz) 2

/-- **Positive-definiteness criterion for strict positivity.** A positive operator whose quadratic
form `re ⟪x, ρ x⟫` is strictly positive on every nonzero `x` is strictly positive. -/
theorem isStrictlyPositive_of_re_inner_self_pos [FiniteDimensional ℂ E] {ρ : E →L[ℂ] E}
    (hpos : 0 ≤ ρ) (hdef : ∀ x : E, x ≠ 0 → 0 < RCLike.re (⟪x, ρ x⟫_ℂ)) :
    IsStrictlyPositive ρ := by
  refine ⟨hpos, ?_⟩
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hd := hdef x hx0
    rw [hx, inner_zero_right, map_zero] at hd
    exact lt_irrefl 0 hd
  exact ⟨hinj, (LinearMap.injective_iff_surjective (K := ℂ)).mp hinj⟩

/-- **A positive operator annihilates the vectors on which its quadratic form vanishes.** For `ρ`
positive and `re ⟪x, ρ x⟫ = 0`, we have `ρ x = 0`. -/
theorem apply_eq_zero_of_re_inner_self_eq_zero {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) {x : E}
    (hx : RCLike.re (⟪x, ρ x⟫_ℂ) = 0) : ρ x = 0 := by
  have hsqrt : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := cfc_real_sqrt_mul_self_of_nonneg hρ
  have hsx : cfc Real.sqrt ρ x = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff]
    rw [← hsqrt, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
      (IsSelfAdjoint.cfc (a := ρ)).adjoint_eq, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow, RCLike.ofReal_re] at hx
    exact hx
  rw [← hsqrt, ContinuousLinearMap.mul_apply, hsx, map_zero]

/-- For a positive CLM `ρ`, `√ρ ∘L (√ρ)† = ρ`. -/
theorem cfc_sqrt_comp_adjoint_eq_self_of_nonneg
    {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) :
    (cfc Real.sqrt ρ).comp (cfc Real.sqrt ρ).adjoint = ρ := by
  rw [IsSelfAdjoint.cfc.adjoint_eq, ← ContinuousLinearMap.mul_def,
    cfc_real_sqrt_mul_self_of_nonneg hρ]

/-- **Unitary-postcomposed canonical factorization**: `(√ρ ∘L W) ∘L (√ρ ∘L W)† = ρ` for any
cross-space `W : F ≃ₗᵢ[ℂ] E` and `0 ≤ ρ`. -/
theorem cfc_sqrt_compL_isometryEquiv_comp_adjoint_eq_self_of_nonneg
    {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (W : F ≃ₗᵢ[ℂ] E) :
    (cfc Real.sqrt ρ ∘L (W : F →L[ℂ] E)) ∘L
      (cfc Real.sqrt ρ ∘L (W : F →L[ℂ] E)).adjoint = ρ := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    (IsSelfAdjoint.cfc (a := ρ)).adjoint_eq,
    ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc (cfc Real.sqrt ρ),
    LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    W.toContinuousLinearEquiv.coe_comp_coe_symm, ContinuousLinearMap.comp_id,
    ← ContinuousLinearMap.mul_def, cfc_real_sqrt_mul_self_of_nonneg hρ]

/-- **CFC sqrt commutes with `conjStarAlgEquiv` on positive operators.** For an isometric
equivalence `e : E ≃ₗᵢ[ℂ] F` and `0 ≤ x : E →L[ℂ] E`, `cfc Real.sqrt (e.conjStarAlgEquiv x) =
e.conjStarAlgEquiv (cfc Real.sqrt x)`. -/
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_cfc_real_sqrt
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (e : E ≃ₗᵢ[ℂ] F) {x : E →L[ℂ] E} (hx : 0 ≤ x) :
    cfc Real.sqrt (e.conjStarAlgEquiv x) = e.conjStarAlgEquiv (cfc Real.sqrt x) := by
  rw [← cfc_real_sqrt_mul_self_eq_self_of_nonneg
      (e.conjStarAlgEquiv_nonneg_iff.mpr (cfc_real_sqrt_nonneg _)),
    ← map_mul, cfc_real_sqrt_mul_self_of_nonneg hx]

/-- **CFC log commutes with `conjStarAlgEquiv`.** For a unitary `e : E ≃ₗᵢ[ℂ] E` and self-adjoint
`τ` whose spectrum avoids `0`, `cfc Real.log (e.conjStarAlgEquiv τ) =
e.conjStarAlgEquiv (cfc Real.log τ)`. -/
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_cfc_real_log [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F] [IsScalarTower ℝ ℂ (E →L[ℂ] E)] [IsScalarTower ℝ ℂ (F →L[ℂ] F)]
    (e : E ≃ₗᵢ[ℂ] F) {τ : E →L[ℂ] E}
    (h : IsSelfAdjoint τ) (hc : ContinuousOn Real.log (spectrum ℝ τ)) :
    cfc Real.log (e.conjStarAlgEquiv τ) = e.conjStarAlgEquiv (cfc Real.log τ) :=
  (StarAlgHom.map_cfc (e.conjStarAlgEquiv : (E →L[ℂ] E) →⋆ₐ[ℂ] (F →L[ℂ] F)) Real.log τ hc
    (e.conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional h
    (e.conjStarAlgEquiv_isSelfAdjoint_iff.mpr h)).symm

/-- **Bilinear sqrt-sandwich** at the CLM level: for `0 ≤ x` and any `Y`, `Z`,
`(√x ∘ Y)† ∘ (√x ∘ Z) = Y† ∘ x ∘ Z`. -/
theorem cfc_sqrt_adjoint_comp_comp_cfc_sqrt_comp_eq
    {x : E →L[ℂ] E} (hx : 0 ≤ x) (Y Z : E →L[ℂ] E) :
    (cfc Real.sqrt x ∘L Y).adjoint ∘L (cfc Real.sqrt x ∘L Z) = Y.adjoint ∘L x ∘L Z := by
  rw [adjoint_comp, (IsSelfAdjoint.cfc (a := x)).adjoint_eq,
    comp_assoc Y.adjoint,
    ← comp_assoc (cfc Real.sqrt x) (cfc Real.sqrt x) Z,
    ← mul_def (cfc Real.sqrt x) (cfc Real.sqrt x),
    cfc_real_sqrt_mul_self_of_nonneg hx]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
/-- **Sqrt-sandwich trace cyclicity**: for a positive operator `x` and any operator `S`, `tr(√x * S
* √x) = tr(S * x)`. -/
theorem trace_cfc_sqrt_sandwich_eq_trace_mul {x : E →L[ℂ] E} (hx : 0 ≤ x) (S : E →L[ℂ] E) :
    LinearMap.trace ℂ E
        ((cfc Real.sqrt x * S * cfc Real.sqrt x : E →L[ℂ] E) : E →ₗ[ℂ] E) =
      LinearMap.trace ℂ E ((S * x : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  rw [mul_assoc, coe_mul, LinearMap.trace_mul_comm, ← coe_mul, mul_assoc,
    cfc_real_sqrt_mul_self_of_nonneg hx]

/-- **HS-norm squared of the CFC square root** equals `re tr x` for a positive operator `x`. -/
theorem re_hsPairing_cfc_sqrt_self_eq_re_trace_of_nonneg
    {x : E →L[ℂ] E} (hx : 0 ≤ x) :
    RCLike.re ((cfc Real.sqrt x).hsPairing (cfc Real.sqrt x)) =
      RCLike.re (LinearMap.trace ℂ E x.toLinearMap) := by
  rw [re_hsPairing_self_eq_re_trace_sq_of_isSelfAdjoint IsSelfAdjoint.cfc,
    cfc_real_sqrt_mul_self_of_nonneg hx]

/-- For a density operator `x`, the HS-norm squared of `cfc Real.sqrt x` equals `1`. -/
theorem IsDensityOp.re_hsPairing_cfc_sqrt_self_eq_one
    {x : E →L[ℂ] E} (hx : x.IsDensityOp) :
    RCLike.re ((cfc Real.sqrt x).hsPairing (cfc Real.sqrt x)) = 1 := by
  rw [re_hsPairing_cfc_sqrt_self_eq_re_trace_of_nonneg hx.nonneg, hx.trace_eq_one, RCLike.one_re]

end

section MaximallyMixed

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F]

omit [CompleteSpace F] in
/-- The **maximally mixed state** `(1/d) • 1` (where `d = dim F`) is a density operator. -/
theorem isDensityOp_finrank_inv_smul_one [Nontrivial F] :
    IsDensityOp ((Module.finrank ℂ F : ℂ)⁻¹ • (1 : F →L[ℂ] F)) := by
  have hd : (Module.finrank ℂ F : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := F)).ne'
  have hnn : (0 : ℂ) ≤ (Module.finrank ℂ F : ℂ)⁻¹ := by
    rw [← RCLike.ofReal_natCast, ← RCLike.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (by positivity)
  refine ⟨isPositive_one.smul_of_nonneg hnn, ?_⟩
  rw [ContinuousLinearMap.coe_smul, map_smul, ContinuousLinearMap.coe_one, LinearMap.trace_one,
    smul_eq_mul, inv_mul_cancel₀ hd]

/-- The **maximally mixed state** `(1/d) • 1` (where `d = dim F`) is strictly positive. -/
theorem isStrictlyPositive_finrank_inv_smul_one [Nontrivial F] :
    IsStrictlyPositive ((Module.finrank ℂ F : ℂ)⁻¹ • (1 : F →L[ℂ] F)) := by
  refine IsStrictlyPositive.smul ?_ isStrictlyPositive_one
  have : (0 : ℝ) < (Module.finrank ℂ F : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.zero_lt_real]
  positivity

end MaximallyMixed

end ContinuousLinearMap
