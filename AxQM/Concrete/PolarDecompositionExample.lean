/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.Matrix.PolarDecomposition

/-!
# Concrete: the polar decompositions of `[[1,0],[1,1]]` (Nielsen & Chuang, Exercise 2.50)

**Nielsen & Chuang, Exercise 2.50 (p. 79)** asks: *find the left and right
polar decompositions of the matrix*
`A = !![1, 0; 1, 1]`  (N&C (2.81)).

## Main results
* `polarExampleUnitary_mem_unitaryGroup` — `U` is unitary.
* `polarExampleLeftFactor_eq_sqrt` / `polarExampleRightFactor_eq_sqrt` — `J = √(A†A)`,
  `K = √(A A†)` as N&C defines them.
* `polarExampleMat_eq_left_polar` — `A = U J` (the left polar decomposition).
* `polarExampleMat_eq_right_polar` — `A = K U` (the right polar decomposition).
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix MatrixOrder ComplexOrder

/-- The matrix `A = [[1,0],[1,1]]` of Nielsen & Chuang (2.81), whose polar decompositions
are computed in this file. -/
def polarExampleMat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The (shared) unitary factor `U = (√5)⁻¹ [[2,-1],[1,2]]` of both polar decompositions. -/
noncomputable def polarExampleUnitary : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • !![2, -1; 1, 2]

/-- The positive factor `J = √(A†A) = (√5)⁻¹ [[3,1],[1,2]]` of the *left* polar decomposition
`A = U J`. -/
noncomputable def polarExampleLeftFactor : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • !![3, 1; 1, 2]

/-- The positive factor `K = √(A A†) = (√5)⁻¹ [[2,1],[1,3]]` of the *right* polar
decomposition `A = K U`. -/
noncomputable def polarExampleRightFactor : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • !![2, 1; 1, 3]

/-- `U` is unitary: `U Uᵀ = 1`. -/
theorem polarExampleUnitary_mem_unitaryGroup :
    polarExampleUnitary ∈ Matrix.unitaryGroup (Fin 2) ℝ := sorry

/-- `J = √(A†A)`: `J` is *the* principal (positive) square root of `A†A`, exactly N&C's
`J ≡ √(A†A)`. -/
theorem polarExampleLeftFactor_eq_sqrt :
    CFC.sqrt (polarExampleMatᴴ * polarExampleMat) = polarExampleLeftFactor := sorry

/-- `K = √(A A†)`: `K` is *the* principal (positive) square root of `A A†`, exactly N&C's
`K ≡ √(A A†)`. -/
theorem polarExampleRightFactor_eq_sqrt :
    CFC.sqrt (polarExampleMat * polarExampleMatᴴ) = polarExampleRightFactor := sorry

/-- **Left polar decomposition** `A = U J` (N&C, `A = U J`): the matrix `A` factors as the
unitary `U` times the positive `J = √(A†A)`. -/
theorem polarExampleMat_eq_left_polar :
    polarExampleMat = polarExampleUnitary * polarExampleLeftFactor := sorry

/-- **Right polar decomposition** `A = K U` (N&C, `A = K U`): the matrix `A` factors as the
positive `K = √(A A†)` times the unitary `U`. -/
theorem polarExampleMat_eq_right_polar :
    polarExampleMat = polarExampleRightFactor * polarExampleUnitary := sorry

end AxQM.Concrete
