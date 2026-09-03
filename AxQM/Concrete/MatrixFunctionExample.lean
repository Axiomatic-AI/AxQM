/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Concrete: square root and logarithm of `[[4,3],[3,4]]` (Nielsen & Chuang, Exercise 2.34)

**Nielsen & Chuang, Exercise 2.34 (p. 75)** asks for a square root
and a logarithm of the matrix
`A = !![4, 3; 3, 4]`  (N&C (2.57)).

## Main results
* `matFourThreeSqrt_mul_self` — `(√A)² = A`, so `√A` is a square root of `A`;
  `matFourThreeSqrt_posDef` pins it down as *the* principal (positive) square root.
* `exp_matFourThreeLog` — `exp(log A) = A`, so `log A` is a logarithm of `A`;
  `matFourThreeLog_isHermitian` records that it is the real-symmetric branch.
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix

/-- The real symmetric matrix `A = [[4,3],[3,4]]` of Nielsen & Chuang (2.57). -/
noncomputable def matFourThree : Matrix (Fin 2) (Fin 2) ℝ := !![4, 3; 3, 4]

/-- The principal square root `√A = [[(1+√7)/2, (√7-1)/2], [(√7-1)/2, (1+√7)/2]]`,
obtained by applying `√·` to the eigenvalues `7` and `1` of `A`. -/
noncomputable def matFourThreeSqrt : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + Real.sqrt 7) / 2, (Real.sqrt 7 - 1) / 2;
     (Real.sqrt 7 - 1) / 2, (1 + Real.sqrt 7) / 2]

/-- `√A` squares to `A`: it is a square root of `A`. -/
theorem matFourThreeSqrt_mul_self : matFourThreeSqrt * matFourThreeSqrt = matFourThree := sorry

/-- `√A` is positive definite. -/
theorem matFourThreeSqrt_posDef : matFourThreeSqrt.PosDef := sorry

/-- The logarithm `log A = (log 7 / 2) • [[1,1],[1,1]]`, obtained by applying `log ·` to the
eigenvalues `7` and `1` of `A` (with `log 1 = 0`). -/
noncomputable def matFourThreeLog : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.log 7 / 2) • !![1, 1; 1, 1]

/-- `log A` is Hermitian (real symmetric): it is the real-symmetric branch of the logarithm. -/
theorem matFourThreeLog_isHermitian : matFourThreeLog.IsHermitian := sorry

/-- `exp(log A) = A`: the matrix `log A` is a logarithm of `A`. -/
theorem exp_matFourThreeLog : NormedSpace.exp matFourThreeLog = matFourThree := sorry

end AxQM.Concrete
