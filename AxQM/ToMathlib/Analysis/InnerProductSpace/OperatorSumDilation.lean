/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryExtension
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The converse system–environment construction: a unitary dilation from a Kraus family

Given a family of operation elements `Eₖ`, this file assembles a dilation
`V : Hin →ₗ Eout ⊗ F` whose operation elements are the `Eₖ`, and — when the family is complete —
extends it to a unitary on the joint system–environment space.

## Main definitions and results

* `LinearMap.krausDilation b E` — the dilation `V = Σₖ embedRight b k ∘ₗ Eₖ`, i.e.
  `V ψ = Σₖ Eₖ ψ ⊗ b k` (Eq. (8.37)).
* `LinearMap.krausOp_krausDilation` — the assembled dilation has the prescribed operation elements:
  `krausOp b (krausDilation b E) k = Eₖ` (Eq. (8.41)).
* `LinearMap.adjoint_krausDilation_comp_self` — `V† V = Σₖ Eₖ† Eₖ`; hence `V` is an isometry **iff**
  the family is complete (`Σₖ Eₖ† Eₖ = 1`, Eq. (8.38)).
* `LinearMap.exists_unitary_krausDilation` — **the unitary (Eq. (8.36))**: for a complete family and
  a unit environment state `ω`, there is a unitary `U : (H ⊗ F) ≃ₗᵢ (H ⊗ F)` with `U (ψ ⊗ ω) =
  krausDilation b E ψ`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (System–environment models; Box 8.1; Exercises 8.8, 8.9).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace LinearMap

section KrausDilation

variable {𝕜 Hin Eout F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Hin] [InnerProductSpace 𝕜 Hin] [FiniteDimensional 𝕜 Hin]
  [NormedAddCommGroup Eout] [InnerProductSpace 𝕜 Eout] [FiniteDimensional 𝕜 Eout]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- The **dilation assembled from a Kraus family** `E : ι → Hin →ₗ Eout` relative to an orthonormal
basis `b` of the environment factor `F`: `V = Σₖ embedRight b k ∘ₗ Eₖ`, that is `V ψ = Σₖ Eₖ ψ ⊗
b k` (Nielsen–Chuang Eq. (8.37)). -/
noncomputable def krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) :
    Hin →ₗ[𝕜] Eout ⊗[𝕜] F :=
  ∑ k, embedRight b k ∘ₗ E k

omit [FiniteDimensional 𝕜 Hin] [FiniteDimensional 𝕜 Eout] [FiniteDimensional 𝕜 F] in
/-- **The assembled dilation recovers the operation elements** (Nielsen–Chuang Eq. (8.41)): the
`k`-th Kraus operator of `krausDilation b E` is `Eₖ`. -/
theorem krausOp_krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) (k : ι) :
    krausOp b (krausDilation b E) k = E k := by
  classical
  ext x
  simp only [krausOp, LinearMap.comp_apply, krausDilation, LinearMap.sum_apply, map_sum,
    embedRight_apply, restrictRight_tmul, b.inner_eq_ite]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **General Kraus identity**: for *any* dilation `V`, `Σₖ (krausOp b V k)† (krausOp b V k) = V†
V`. -/
theorem sum_adjoint_krausOp_comp_krausOp_eq (b : OrthonormalBasis ι 𝕜 F)
    (V : Hin →ₗ[𝕜] Eout ⊗[𝕜] F) :
    ∑ k, adjoint (krausOp b V k) ∘ₗ krausOp b V k = adjoint V ∘ₗ V := by
  ext x
  simp only [LinearMap.sum_apply, krausOp, adjoint_comp, adjoint_restrictRight,
    LinearMap.comp_apply]
  rw [← map_sum]
  congr 1
  calc ∑ k, embedRight b k (restrictRight b k (V x))
      = (∑ k, embedRight b k ∘ₗ restrictRight b k) (V x) := by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    _ = V x := by rw [sum_embedRight_comp_restrictRight, LinearMap.id_apply]

/-- **`V† V = Σₖ Eₖ† Eₖ`** for the assembled dilation `V = krausDilation b E`. Consequently `V` is
an **isometry** (`V† V = 1`) **iff** the family is **complete** (`Σₖ Eₖ† Eₖ = 1`) —
Nielsen–Chuang Eq. (8.38). -/
theorem adjoint_krausDilation_comp_self (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) :
    adjoint (krausDilation b E) ∘ₗ krausDilation b E = ∑ k, adjoint (E k) ∘ₗ E k := by
  rw [← sum_adjoint_krausOp_comp_krausOp_eq b (krausDilation b E)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [krausOp_krausDilation]

/-- **The assembled dilation is an isometry when the family is complete** (`Σₖ Eₖ† Eₖ = 1`): then
`V† V = 1`. -/
theorem adjoint_krausDilation_comp_self_eq_id (b : OrthonormalBasis ι 𝕜 F)
    (E : ι → Hin →ₗ[𝕜] Eout) (hE : ∑ k, adjoint (E k) ∘ₗ E k = LinearMap.id) :
    adjoint (krausDilation b E) ∘ₗ krausDilation b E = LinearMap.id := by
  rw [adjoint_krausDilation_comp_self, hE]

end KrausDilation

section Unitary

variable {𝕜 H F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- **The system–environment unitary** (Nielsen–Chuang Eq. (8.36)): a complete Kraus family,
acting on an environment prepared in a unit state `ω`, is implemented by a unitary on the joint
state space. -/
theorem exists_unitary_krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → H →ₗ[𝕜] H)
    (hE : ∑ k, adjoint (E k) ∘ₗ E k = LinearMap.id) {ω : F} (hω : ‖ω‖ = 1) :
    ∃ U : (H ⊗[𝕜] F) ≃ₗᵢ[𝕜] (H ⊗[𝕜] F), ∀ ψ : H, U (ψ ⊗ₜ[𝕜] ω) = krausDilation b E ψ := by
  set V := krausDilation b E with hVdef
  have hViso : ∀ x y : H, ⟪V x, V y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
    intro x y
    rw [← adjoint_inner_right, ← LinearMap.comp_apply,
      adjoint_krausDilation_comp_self_eq_id b E hE, LinearMap.id_apply]
  have hωω : ⟪ω, ω⟫_𝕜 = 1 := by rw [inner_self_eq_norm_sq_to_K, hω]; simp
  set W : Submodule 𝕜 (H ⊗[𝕜] F) := LinearMap.range (tmulRightVec ω) with hWdef
  set g₀ : (H ⊗[𝕜] F) →ₗ[𝕜] (H ⊗[𝕜] F) := V ∘ₗ contractRightVec ω with hg₀def
  have hg₀ : ∀ ψ : H, g₀ (ψ ⊗ₜ[𝕜] ω) = V ψ := by
    intro ψ
    simp only [hg₀def, LinearMap.comp_apply, contractRightVec_tmul, hωω, one_smul]
  set g : ↥W →ₗ[𝕜] (H ⊗[𝕜] F) := g₀.domRestrict W with hgdef
  have hg : ∀ w₁ w₂ : ↥W, ⟪g w₁, g w₂⟫_𝕜 = ⟪w₁, w₂⟫_𝕜 := by
    intro w₁ w₂
    obtain ⟨ψ₁, hψ₁⟩ := LinearMap.mem_range.mp w₁.2
    obtain ⟨ψ₂, hψ₂⟩ := LinearMap.mem_range.mp w₂.2
    have e₁ : (↑w₁ : H ⊗[𝕜] F) = ψ₁ ⊗ₜ[𝕜] ω := by rw [← hψ₁, tmulRightVec_apply]
    have e₂ : (↑w₂ : H ⊗[𝕜] F) = ψ₂ ⊗ₜ[𝕜] ω := by rw [← hψ₂, tmulRightVec_apply]
    rw [hgdef, LinearMap.domRestrict_apply, LinearMap.domRestrict_apply, e₁, e₂, hg₀, hg₀, hViso,
      Submodule.coe_inner, e₁, e₂, TensorProduct.inner_tmul, hωω, mul_one]
  refine ⟨g.unitaryExtend hg, fun ψ => ?_⟩
  have hmem : ψ ⊗ₜ[𝕜] ω ∈ W := LinearMap.mem_range.mpr ⟨ψ, tmulRightVec_apply ω ψ⟩
  calc (g.unitaryExtend hg) (ψ ⊗ₜ[𝕜] ω)
      = g ⟨ψ ⊗ₜ[𝕜] ω, hmem⟩ := g.unitaryExtend_apply hg ⟨ψ ⊗ₜ[𝕜] ω, hmem⟩
    _ = g₀ (ψ ⊗ₜ[𝕜] ω) := by rw [hgdef, LinearMap.domRestrict_apply]
    _ = V ψ := hg₀ ψ

end Unitary

end LinearMap

namespace ContinuousLinearMap

-- Both instance families are load-bearing: `ContinuousLinearMap.adjoint` needs `[CompleteSpace _]`,
-- which is not synthesized from `[FiniteDimensional ℂ _]`, and `LinearMap.adjoint` needs
-- `[FiniteDimensional ℂ _]`.
variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- **The `LinearMap`-level completeness relation from the `ContinuousLinearMap` one.** For an
operator family `E : ι → H →L[ℂ] G`, the completeness relation `∑ᵢ Eᵢ† Eᵢ = 1` (in the
`ContinuousLinearMap` algebra) transports along the `→ₗ` coercion to the `LinearMap` form `∑ᵢ
(Eᵢ†)ₗ ∘ₗ (Eᵢ)ₗ = 1ₗ`. -/
theorem sum_adjoint_comp_toLinearMap_eq_id (E : ι → H →L[ℂ] G)
    (hE : ∑ i, adjoint (E i) ∘L E i = 1) :
    ∑ i, LinearMap.adjoint ((E i).toLinearMap) ∘ₗ (E i).toLinearMap = LinearMap.id := by
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x) hE
  simpa only [coe_sum, sum_apply, comp_apply, one_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, coe_coe, ← adjoint_toLinearMap, LinearMap.id_apply] using h

end ContinuousLinearMap
