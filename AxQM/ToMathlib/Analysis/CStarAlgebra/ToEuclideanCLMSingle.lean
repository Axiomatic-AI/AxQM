/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Action of `Matrix.toEuclideanCLM` on a standard basis vector

`Matrix.toEuclideanCLM M` is the continuous linear operator on `EuclideanSpace 𝕜 n` corresponding to
a square matrix `M` (via the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`). This file records the
elementary fact that it sends the standard basis vector `|j⟩ = EuclideanSpace.single j 1` to the
`j`-th **column** of `M`, expressed as the superposition `∑ₖ Mₖⱼ |k⟩`.

## Main statements

* `Matrix.toEuclideanCLM_apply_single` : `toEuclideanCLM M |j⟩ = ∑ₖ Mₖⱼ |k⟩`.
-/

@[expose] public section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Action of `Matrix.toEuclideanCLM` on a standard basis vector:** the operator
`Matrix.toEuclideanCLM M` sends `|j⟩ = EuclideanSpace.single j 1` to the `j`-th column of `M`,
`∑ₖ Mₖⱼ |k⟩`. -/
theorem toEuclideanCLM_apply_single (M : Matrix n n 𝕜) (j : n) :
    Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) M (EuclideanSpace.single j (1 : 𝕜))
      = ∑ k : n, (M k j) • EuclideanSpace.single k (1 : 𝕜) := by
  ext m
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Pi.single_apply]

end Matrix
