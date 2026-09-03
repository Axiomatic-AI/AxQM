/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity and trace of `Matrix.toEuclideanCLM`

`Matrix.toEuclideanCLM` is the `⋆`-algebra equivalence sending a square matrix `A : Matrix n n 𝕜`
to the continuous linear endomorphism of `EuclideanSpace 𝕜 n` it represents in the standard
orthonormal basis. This file records several of its properties.
-/

open scoped InnerProductSpace ComplexOrder

@[expose] public section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **`Matrix.toEuclideanCLM A` is positive iff `A` is positive semidefinite.** -/
theorem isPositive_toEuclideanCLM_iff (A : Matrix n n 𝕜) :
    (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, coe_toEuclideanCLM_eq_toEuclideanLin,
    isPositive_toEuclideanLin_iff]

/-- **The operator trace of `Matrix.toEuclideanCLM A` is the matrix trace `A.trace`.** -/
theorem trace_toEuclideanCLM (A : Matrix n n 𝕜) :
    LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n) ↑(Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) A)
      = A.trace := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq]

end Matrix
