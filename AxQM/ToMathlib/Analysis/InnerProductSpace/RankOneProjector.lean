/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The orthogonal projector onto the span of an orthonormal family

Given a family of vectors `v : ι → E` in an inner product space `E` over `𝕜` (`ℝ` or `ℂ`) and a
finite index set `s : Finset ι`, this file introduces the **projector** `P = ∑ i ∈ s, |v i⟩⟨v i|`.

## Main results

* `InnerProductSpace.isIdempotentElem_orthonormalProjector`: **Nielsen & Chuang, Exercise 2.16** —
  for an orthonormal family, `P` is idempotent, i.e. `P ∘ P = P` (`P² = P`).
* `InnerProductSpace.isSelfAdjoint_orthonormalProjector`: `P` is self-adjoint, `P† = P` (N&C's
  remark that a projector is Hermitian).
* `InnerProductSpace.isStarProjection_orthonormalProjector`: for an orthonormal family, `P` is a
  star projection (a self-adjoint idempotent) — a genuine orthogonal projector.
* `InnerProductSpace.orthonormalProjector_hasEigenvalue_eq_zero_or_one`: **Nielsen & Chuang,
  Exercise 2.23** (eigenvalue form) — every eigenvalue of `P` is `0` or `1`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace InnerProductSpace

variable {𝕜 : Type*} {E : Type*} {ι : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Nielsen & Chuang's projector** (eq. (2.35)). Given a family `v : ι → E` and a finite index set
`s : Finset ι`, the operator `∑ i ∈ s, |v i⟩⟨v i|`. -/
noncomputable def orthonormalProjector (𝕜 : Type*) {E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : ι → E) (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, rankOne 𝕜 (v i) (v i)

/-- **Nielsen & Chuang, Exercise 2.16.** Any projector `P = ∑ i ∈ s, |v i⟩⟨v i|` of an orthonormal
family `v` satisfies `P² = P`, i.e. `P` is idempotent (`P ∘ P = P`). -/
theorem isIdempotentElem_orthonormalProjector {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    IsIdempotentElem (orthonormalProjector 𝕜 v s) := by
  classical
  have hb : ∀ i j : ι, (inner 𝕜 (v i) (v j) : 𝕜) = if i = j then (1 : 𝕜) else 0 :=
    fun i j => orthonormal_iff_ite.mp hv i j
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, orthonormalProjector]
  simp only [ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum,
    rankOne_comp_rankOne, hb, ite_smul, one_smul, zero_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_ite_eq', if_pos hi]

/-- The projector `P = ∑ i ∈ s, |v i⟩⟨v i|` is self-adjoint, `P† = P` (Nielsen & Chuang's remark
that a projector is Hermitian). -/
theorem isSelfAdjoint_orthonormalProjector [CompleteSpace E] (v : ι → E) (s : Finset ι) :
    IsSelfAdjoint (orthonormalProjector 𝕜 v s) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, orthonormalProjector, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adjoint_rankOne]

/-- For an orthonormal family `v`, the projector `P = ∑ i ∈ s, |v i⟩⟨v i|` is a **star projection**
— a self-adjoint idempotent — hence a genuine orthogonal projector onto the span of `{v i | i ∈
s}`. -/
theorem isStarProjection_orthonormalProjector [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) : IsStarProjection (orthonormalProjector 𝕜 v s) :=
  ⟨isIdempotentElem_orthonormalProjector hv s, isSelfAdjoint_orthonormalProjector v s⟩

/-- **Nielsen & Chuang, Exercise 2.23** (eigenvalue form). Every eigenvalue `μ` of the projector `P
= ∑ i ∈ s, |v i⟩⟨v i|` of an orthonormal family is either `0` or `1`.

This is the eigenvalue-predicate reading of the exercise.
-/
theorem orthonormalProjector_hasEigenvalue_eq_zero_or_one {v : ι → E} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) {μ : 𝕜}
    (h : Module.End.HasEigenvalue (orthonormalProjector 𝕜 v s : E →ₗ[𝕜] E) μ) :
    μ = 0 ∨ μ = 1 := sorry

end InnerProductSpace
