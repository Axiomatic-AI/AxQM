/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A matrix that is not diagonalizable (Nielsen & Chuang, Exercise 2.12)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.12
(p. 69) asks to prove that a `2 × 2` matrix is not diagonalizable.

## Main declarations
* `shearMatrix` — the matrix `!![1, 0; 1, 1]` of N&C (2.31), a complex `2 × 2`
  matrix (a shear / unipotent matrix).
* `shearMatrix_not_diagonalizable` — the exercise: `shearMatrix` is not similar
  to any diagonal matrix.
-/

namespace AxQM.Concrete

open scoped Matrix

/-- **Nielsen & Chuang, Exercise 2.12**, the matrix `!![1, 0; 1, 1]` of N&C
(2.31): a complex `2 × 2` shear (unipotent) matrix. -/
def shearMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 1]

/-- **Nielsen & Chuang, Exercise 2.12.** The matrix `!![1, 0; 1, 1]` is not diagonalizable. (This is
stronger than N&C's orthonormal notion of diagonalizability, which it therefore also refutes.) -/
theorem shearMatrix_not_diagonalizable :
    ¬ ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ),
      IsUnit P ∧ shearMatrix = P * Matrix.diagonal d * P⁻¹ := sorry

end AxQM.Concrete
