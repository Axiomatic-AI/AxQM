/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.Matricization
public import AxQM.ToMathlib.Analysis.InnerProductSpace.PostMeasurement
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# The operator-sum (Kraus) map, and unitary freedom in its representation

For a finite family of operators `E : ι → (H →L[ℂ] G)` — each mapping an input
space `H` to an output space `G` — the **operator-sum map** sends an operator `ρ`
on `H` to
`Σᵢ Eᵢ ρ Eᵢ†`
on `G`. A quantum operation admits the form `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` with `Σᵢ Eᵢ† Eᵢ ≤ 1`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (Theorems 8.1, 8.2; Exercise 8.3).
-/

open scoped InnerProductSpace TensorProduct

@[expose] public section

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- The **operator-sum (Kraus) map** of a finite family `E : ι → (H →L[ℂ] G)`, as a
`ℂ`-linear map in the operator argument: `ρ ↦ Σᵢ Eᵢ ρ Eᵢ†`. -/
noncomputable def krausSumₗ (E : ι → H →L[ℂ] G) :
    (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G) where
  toFun ρ := ∑ i, (E i) ∘L ρ ∘L adjoint (E i)
  map_add' ρ σ := by
    simp only [add_comp, comp_add, Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [smul_comp, comp_smul, RingHom.id_apply, Finset.smul_sum]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
@[simp]
theorem krausSumₗ_apply (E : ι → H →L[ℂ] G) (ρ : H →L[ℂ] H) :
    krausSumₗ E ρ = ∑ i, (E i) ∘L ρ ∘L adjoint (E i) := rfl

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- The operator-sum map preserves positivity. -/
theorem krausSumₗ_isPositive (E : ι → H →L[ℂ] G) {ρ : H →L[ℂ] H}
    (hρ : ρ.IsPositive) : (krausSumₗ E ρ).IsPositive := by
  rw [krausSumₗ_apply]
  exact isPositive_sum Finset.univ fun i _ => hρ.conj_adjoint (E i)

/-- Cyclicity of the trace for a single summand: `tr(E ρ E†) = tr(E† E ρ)`, moving
the output-space factor `E` around the cycle back to the input space. -/
theorem trace_conj_adjoint (E : H →L[ℂ] G) (ρ : H →L[ℂ] H) :
    LinearMap.trace ℂ G ((E ∘L ρ ∘L adjoint E : G →L[ℂ] G) : G →ₗ[ℂ] G)
      = LinearMap.trace ℂ H ((adjoint E ∘L E ∘L ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  simp only [ContinuousLinearMap.coe_comp]
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc]

/-- **The operator-sum trace identity.** The trace of `Σᵢ Eᵢ ρ Eᵢ†` on the output
space equals the trace of `(Σᵢ Eᵢ† Eᵢ) ρ` on the input space:
`tr(Σᵢ Eᵢ ρ Eᵢ†) = tr((Σᵢ Eᵢ† Eᵢ) ρ)`. -/
theorem trace_krausSumₗ (E : ι → H →L[ℂ] G) (ρ : H →L[ℂ] H) :
    LinearMap.trace ℂ G ((krausSumₗ E ρ : G →L[ℂ] G) : G →ₗ[ℂ] G)
      = LinearMap.trace ℂ H
          (((∑ i, adjoint (E i) ∘L E i) ∘L ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  rw [krausSumₗ_apply, ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.coe_sum,
    map_sum, ContinuousLinearMap.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_conj_adjoint (E i) ρ, ← ContinuousLinearMap.comp_assoc]

/-- **The Kraus map of a completeness-satisfying family sends density operators to density
operators.** If `∑ᵢ Eᵢ† Eᵢ = I` and `ρ` is a density operator, then `∑ᵢ Eᵢ ρ Eᵢ†` is again a
density operator. -/
theorem isDensityOp_krausSumₗ (E : ι → H →L[ℂ] H)
    (hE : ∑ i, adjoint (E i) ∘L E i = 1) {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) :
    (krausSumₗ E ρ).IsDensityOp := by
  rw [isDensityOp_iff]
  refine ⟨krausSumₗ_isPositive E hρ.isPositive, ?_⟩
  rw [trace_krausSumₗ, hE, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  exact hρ.trace_eq_one

/-- **Unitary freedom in the operator-sum representation** (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, **Theorem 8.2**). Two equal-size families `E`, `F` of operation elements
on a single finite-dimensional complex inner product space (the "padded" form — pad the shorter
list with zero operators so both are indexed by the common `ι`) give **the same operator-sum map**,
`krausSumₗ E = krausSumₗ F` (i.e. `∀ ρ, ∑ᵢ Eᵢ ρ Eᵢ† = ∑ⱼ Fⱼ ρ Fⱼ†`), **iff** their operation
elements are related by a unitary coefficient matrix `u ∈ Matrix.unitaryGroup ι ℂ`:
`Eᵢ = ∑ⱼ uᵢⱼ Fⱼ`.
-/
theorem krausSumₗ_eq_iff_exists_mem_unitaryGroup [DecidableEq ι] {E F : ι → H →L[ℂ] H} :
    krausSumₗ E = krausSumₗ F ↔
      ∃ u ∈ Matrix.unitaryGroup ι ℂ, ∀ i, E i = ∑ j, u i j • F j := sorry

end ContinuousLinearMap

namespace LinearMap

section KrausFromDilation

variable {𝕜 Hin E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Hin] [InnerProductSpace 𝕜 Hin] [FiniteDimensional 𝕜 Hin]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- The `k`-th **operation element** (Kraus operator) of a dilation `V : Hin →ₗ E ⊗ F` relative to
an orthonormal basis `b` of the traced-out factor `F`: `Eₖ = ⟨b k| V`, that is
`restrictRight b k ∘ₗ V : Hin →ₗ E`, the map `V` followed by contracting the `F`-slot against `b k`.
Its input space `Hin` and output space `E` need not agree. -/
noncomputable def krausOp (b : OrthonormalBasis ι 𝕜 F) (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (k : ι) :
    Hin →ₗ[𝕜] E :=
  restrictRight b k ∘ₗ V

end KrausFromDilation

section AncillaDilation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The **ancilla embedding**: tensoring with a fixed vector `ω : F`, `x ↦ x ⊗ₜ ω`, as a linear map
`E →ₗ E ⊗ F`. -/
noncomputable def tmulRightVec (ω : F) : E →ₗ[𝕜] E ⊗[𝕜] F :=
  (TensorProduct.mk 𝕜 E F).flip ω

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem tmulRightVec_apply (ω : F) (x : E) : tmulRightVec ω x = x ⊗ₜ[𝕜] ω := rfl

/-- The **contraction against a fixed vector** `ω : F`, `x ⊗ₜ y ↦ ⟪ω, y⟫ • x`, as a linear map `E ⊗
F →ₗ E`. -/
noncomputable def contractRightVec (ω : F) : E ⊗[𝕜] F →ₗ[𝕜] E :=
  (TensorProduct.rid 𝕜 E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (innerSL 𝕜 ω).toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem contractRightVec_tmul (ω : F) (x : E) (y : F) :
    contractRightVec ω (x ⊗ₜ[𝕜] y) = ⟪ω, y⟫_𝕜 • x := rfl

end AncillaDilation

end LinearMap
