/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix representation of a rank-one operator in an orthonormal basis

Let `b` be an orthonormal basis (indexed by a finite type `n`) of a finite-dimensional inner
product space `E` over `𝕜` (`ℝ` or `ℂ`). This file computes the matrix, with respect to `b`, of the
rank-one "ket-bra" operator `|b j⟩⟨b k| = InnerProductSpace.rankOne 𝕜 (b j) (b k)`, which sends
`z ↦ ⟪b k, z⟫ • b j`.

## Main result

* `LinearMap.toMatrixOrthonormal_rankOne`: the matrix of `|b j⟩⟨b k|` in the basis `b` is the
  single-entry matrix `Matrix.single j k 1` — a `1` at row `j`, column `k`, and `0` elsewhere.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {n : Type*} [Fintype n] [DecidableEq n] [FiniteDimensional 𝕜 E]

/-- **Nielsen & Chuang, Exercise 2.10.** With respect to an orthonormal basis `b` of a
finite-dimensional inner product space, the matrix of the rank-one operator `|b j⟩⟨b k|`
(`InnerProductSpace.rankOne 𝕜 (b j) (b k)`, sending `z ↦ ⟪b k, z⟫ • b j`) is the single-entry
matrix `Matrix.single j k 1`, i.e. a `1` at row `j`, column `k`, and `0` elsewhere. -/
theorem toMatrixOrthonormal_rankOne (b : OrthonormalBasis n 𝕜 E) (j k : n) :
    toMatrixOrthonormal b (InnerProductSpace.rankOne 𝕜 (b j) (b k) : E →ₗ[𝕜] E)
      = Matrix.single j k 1 := sorry

end LinearMap
