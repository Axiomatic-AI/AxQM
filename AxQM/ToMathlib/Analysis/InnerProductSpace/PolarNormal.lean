/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PolarUnitary
public import AxQM.ToMathlib.Analysis.InnerProductSpace.NormalOperator

/-!

# Polar decomposition of a normal operator in outer-product form

A *normal* operator `A` on a finite-dimensional complex inner product space is diagonal in an
orthonormal eigenbasis `{bᵢ}`, and this file gives its polar decomposition in that form.

## The diagonal operator

* `OrthonormalBasis.diagonalOperator_comp`: `diag w ∘L diag w' = diag (w * w')` — composition is
  pointwise multiplication of diagonals;
* `OrthonormalBasis.diagonalOperator_adjoint`: `(diag w)† = diag (star w)`;
* `OrthonormalBasis.diagonalOperator_one`: `diag 1 = 1`;
* `OrthonormalBasis.diagonalOperator_mem_unitary`: `diag w` is unitary when `‖wᵢ‖ = 1`;
* `OrthonormalBasis.diagonalOperator_isPositive_of_nonneg`: `diag w` is positive when `0 ≤ wᵢ`;

## Main results (N&C Exercise 2.49)

* `OrthonormalBasis.diagonalOperator_eq_phase_comp_norm`: `A = U ∘L J` (left polar decomposition);
* `OrthonormalBasis.diagonalOperator_eq_norm_comp_phase`: `A = J ∘L U` (right polar decomposition);
* `OrthonormalBasis.diagonalOperator_phase_mem_unitary`: `U` is unitary;
* `OrthonormalBasis.diagonalOperator_norm_isPositive`: `J` is positive;
* `OrthonormalBasis.diagonalOperator_norm_eq_absoluteValue`: `J = |A| = √(A† A)`.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate ComplexOrder

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **phase** (unit-modulus part) of a scalar: `phase z = z / ‖z‖` for `z ≠ 0`, and
`phase 0 = 1`. -/
noncomputable def phase (z : 𝕜) : 𝕜 := if z = 0 then 1 else (‖z‖ : 𝕜)⁻¹ * z

end RCLike

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The operator **diagonal in an orthonormal basis** `b` with diagonal entries `w`:
`diagonalOperator b w = ∑ᵢ wᵢ • |bᵢ⟩⟨bᵢ|`. -/
noncomputable def diagonalOperator (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) : E →L[𝕜] E :=
  ∑ i, w i • rankOne 𝕜 (b i) (b i)

/-- The diagonal operator with all-ones diagonal is the identity. -/
@[simp] theorem diagonalOperator_one (b : OrthonormalBasis ι 𝕜 E) :
    b.diagonalOperator 1 = 1 := by
  simp only [diagonalOperator, Pi.one_apply, one_smul]
  exact b.sum_rankOne_eq_id

/-- **Composition of diagonal operators is pointwise multiplication of their diagonals**:
`diag w ∘L diag w' = diag (w * w')`. -/
theorem diagonalOperator_comp (b : OrthonormalBasis ι 𝕜 E) (w w' : ι → 𝕜) :
    b.diagonalOperator w ∘L b.diagonalOperator w' = b.diagonalOperator (w * w') := by
  simp only [diagonalOperator]
  rw [ContinuousLinearMap.finset_sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_finset_sum, Finset.smul_sum,
    Finset.sum_eq_single i]
  · rw [ContinuousLinearMap.comp_smul, rankOne_comp_rankOne, b.inner_eq_one i, one_smul,
      smul_smul, Pi.mul_apply]
  · intro j _ hji
    rw [ContinuousLinearMap.comp_smul, rankOne_comp_rankOne, b.orthonormal.inner_eq_zero
      (Ne.symm hji), zero_smul, smul_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **N&C Exercise 2.49 — left polar decomposition in outer-product form.** For a normal operator
`A = ∑ᵢ μᵢ • |bᵢ⟩⟨bᵢ|`, the left polar decomposition `A = U J` has unitary factor
`U = ∑ᵢ phase(μᵢ) • |bᵢ⟩⟨bᵢ|` and positive factor `J = ∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|`, both diagonal in
`A`'s eigenbasis. -/
theorem diagonalOperator_eq_phase_comp_norm (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator μ =
      b.diagonalOperator (fun i => RCLike.phase (μ i)) ∘L
        b.diagonalOperator (fun i => (‖μ i‖ : 𝕜)) := sorry

/-- **N&C Exercise 2.49 — right polar decomposition in outer-product form.** `A = J U` also holds,
with the same unitary factor `U` and positive factor `J`. -/
theorem diagonalOperator_eq_norm_comp_phase (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator μ =
      b.diagonalOperator (fun i => (‖μ i‖ : 𝕜)) ∘L
        b.diagonalOperator (fun i => RCLike.phase (μ i)) := sorry

variable [CompleteSpace E]

/-- The adjoint of a diagonal operator is diagonal with conjugated entries:
`(diag w)† = diag (star w)`. -/
theorem diagonalOperator_adjoint (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) :
    adjoint (b.diagonalOperator w) = b.diagonalOperator (star w) := by
  simp only [diagonalOperator, map_sum, map_smulₛₗ, InnerProductSpace.adjoint_rankOne,
    Pi.star_apply, RCLike.star_def]

/-- A diagonal operator with unit-modulus diagonal is **unitary**. -/
theorem diagonalOperator_mem_unitary (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜)
    (hw : ∀ i, ‖w i‖ = 1) : b.diagonalOperator w ∈ unitary (E →L[𝕜] E) := by
  have hl : star w * w = 1 := by
    ext i; simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, RCLike.star_def]
    rw [RCLike.conj_mul, hw i]; norm_num
  have hr : w * star w = 1 := by
    ext i; simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, RCLike.star_def]
    rw [RCLike.mul_conj, hw i]; norm_num
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, diagonalOperator_adjoint,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, diagonalOperator_comp,
    diagonalOperator_comp, hl, hr, diagonalOperator_one]
  exact ⟨rfl, rfl⟩

omit [CompleteSpace E] in
/-- A diagonal operator with nonnegative diagonal is **positive**. -/
theorem diagonalOperator_isPositive_of_nonneg (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜)
    (hw : ∀ i, 0 ≤ w i) : (b.diagonalOperator w).IsPositive := by
  rw [diagonalOperator]
  refine isPositive_sum _ fun i _ => ?_
  exact (InnerProductSpace.isPositive_rankOne_self _).smul_of_nonneg (hw i)

/-- The phase factor `U = ∑ᵢ phase(μᵢ) • |bᵢ⟩⟨bᵢ|` is unitary. -/
theorem diagonalOperator_phase_mem_unitary (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator (fun i => RCLike.phase (μ i)) ∈ unitary (E →L[𝕜] E) := sorry

omit [CompleteSpace E] in
/-- The positive factor `J = ∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|` is positive. -/
theorem diagonalOperator_norm_isPositive (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    (b.diagonalOperator (fun i => (‖μ i‖ : 𝕜))).IsPositive := sorry

/-- **The positive factor is the canonical one:** `J = |A| = √(A† A)`. -/
theorem diagonalOperator_norm_eq_absoluteValue [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator (fun i => (‖μ i‖ : 𝕜)) = (b.diagonalOperator μ).absoluteValue := sorry

end OrthonormalBasis

section Normal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

open Module

/-- **Every normal operator is diagonal in an orthonormal eigenbasis, in outer-product form**:
`A = ∑ᵢ μᵢ • |bᵢ⟩⟨bᵢ| = b.diagonalOperator μ`. -/
theorem IsStarNormal.exists_eq_diagonalOperator {A : E →L[ℂ] E} (hA : IsStarNormal A) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (μ : Fin (finrank ℂ E) → ℂ),
      A = b.diagonalOperator μ := sorry

end Normal
