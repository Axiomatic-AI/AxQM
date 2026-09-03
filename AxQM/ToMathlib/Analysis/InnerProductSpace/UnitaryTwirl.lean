/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PolarNormal

/-!
# Sign-diagonal unitaries of an orthonormal basis

Fix an orthonormal basis `b = {bᵢ}` of a finite-dimensional inner product space `E`. For a sign
pattern `ε : ι → Bool` the **sign-diagonal unitary** is the diagonal operator
`∑ᵢ (-1)^{ε i} • |bᵢ⟩⟨bᵢ|`.

## Main definitions

* `OrthonormalBasis.signDiagonal` — the sign-diagonal unitary `∑ᵢ (-1)^{ε i} • |bᵢ⟩⟨bᵢ|`.

## Main results

* `OrthonormalBasis.diagonalOperator_apply_self`, `OrthonormalBasis.inner_diagonalOperator` —
  reusable basis-computation helpers for `diagonalOperator`.
* `OrthonormalBasis.signDiagonal_mem_unitary` — the sign-diagonal operator is unitary.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis ι 𝕜 E)

/-- **Action of a diagonal operator on a basis vector**: `(∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|)(b q) = w q • b q`. -/
theorem diagonalOperator_apply_self (w : ι → 𝕜) (q : ι) :
    b.diagonalOperator w (b q) = w q • b q := by
  rw [diagonalOperator, ContinuousLinearMap.sum_apply, Finset.sum_eq_single q]
  · rw [ContinuousLinearMap.smul_apply, rankOne_apply, b.inner_eq_one, one_smul]
  · intro i _ hi
    rw [ContinuousLinearMap.smul_apply, rankOne_apply, b.inner_eq_zero hi, zero_smul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

/-- **Inner product of a basis vector with a diagonal operator applied to any vector**:
`⟨b p, (∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|) v⟩ = w p · ⟨b p, v⟩`. -/
theorem inner_diagonalOperator (w : ι → 𝕜) (p : ι) (v : E) :
    inner 𝕜 (b p) (b.diagonalOperator w v) = w p * inner 𝕜 (b p) v := by
  rw [diagonalOperator, ContinuousLinearMap.sum_apply, inner_sum, Finset.sum_eq_single p]
  · rw [ContinuousLinearMap.smul_apply, rankOne_apply, inner_smul_right, inner_smul_right,
      b.inner_eq_one, mul_one]
  · intro i _ hi
    rw [ContinuousLinearMap.smul_apply, rankOne_apply, inner_smul_right, inner_smul_right,
      b.inner_eq_zero (Ne.symm hi), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- The **sign-diagonal unitary** for a sign pattern `ε`: `∑ᵢ (-1)^{ε i} • |bᵢ⟩⟨bᵢ|`, the diagonal
operator with `±1` diagonal entries. -/
noncomputable def signDiagonal (ε : ι → Bool) : E →L[𝕜] E :=
  b.diagonalOperator (fun i => if ε i then (-1 : 𝕜) else 1)

section CompleteSpace

variable [CompleteSpace E]

/-- The sign-diagonal operator is **unitary**. -/
theorem signDiagonal_mem_unitary (ε : ι → Bool) :
    b.signDiagonal ε ∈ unitary (E →L[𝕜] E) := by
  refine b.diagonalOperator_mem_unitary _ fun i => ?_
  cases ε i <;> simp

end CompleteSpace

end OrthonormalBasis
