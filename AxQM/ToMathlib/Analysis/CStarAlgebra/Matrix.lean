/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Conjugate transpose and the operator adjoint under `Matrix.toEuclideanCLM`

## Main results

* `Matrix.toEuclideanCLM_conjTranspose_eq_adjoint`: `toEuclideanCLM Aᴴ` is the adjoint of
  `toEuclideanCLM A`.

-/

@[expose] public section

namespace Matrix

section
open WithLp
open scoped Matrix
variable {𝕜 m n l E : Type*}
open LinearMap
variable [RCLike 𝕜]
variable [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l]

/-- `Matrix.toEuclideanCLM` intertwines conjugate transpose with the operator adjoint:
`toEuclideanCLM Aᴴ = (toEuclideanCLM A)†`. -/
lemma toEuclideanCLM_conjTranspose_eq_adjoint (A : Matrix n n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) Aᴴ
      = ContinuousLinearMap.adjoint (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, Matrix.star_eq_conjTranspose]

end

end Matrix
