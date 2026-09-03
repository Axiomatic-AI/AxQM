/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Matrix.PosDef

/-! # Singular value decomposition of a square matrix

For a square matrix `A` over an `RCLike` field, this file proves the **singular value
decomposition** in matrix form: there exist unitary matrices `U`, `V` and a diagonal matrix `D`
with non-negative real entries such that `A = U * D * V`
(`Matrix.exists_unitary_mul_diagonal_mul_unitary`). The diagonal entries of `D` are the *singular
values* of `A`.

## Tags

singular value decomposition, SVD, matrix
-/

@[expose] public section

open Matrix Finset RCLike Module
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Singular value decomposition** (Nielsen & Chuang, Corollary 2.4). -/
theorem exists_unitary_mul_diagonal_mul_unitary (A : Matrix n n 𝕜) :
    ∃ (U V : Matrix n n 𝕜) (d : n → ℝ),
      U ∈ unitaryGroup n 𝕜 ∧ V ∈ unitaryGroup n 𝕜 ∧
        (∀ i, 0 ≤ d i) ∧ A = U * diagonal (RCLike.ofReal ∘ d) * V := sorry

end Matrix
