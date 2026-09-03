/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation

/-!
# Concrete: conjugating the single-qubit rotations by Pauli-`X` (Nielsen & Chuang, Exercise 4.7)

Nielsen & Chuang, Exercise 4.7 asks to show `X Y X = -Y` and to use it to prove `X R_y(θ) X =
R_y(-θ)`.

## Main declarations
* `pauliX_mul_pauliY_mul_pauliX` — `X Y X = -Y` (Exercise 4.7, first part).
* `pauliX_mul_rotY_mul_pauliX` — `X R_y(θ) X = R_y(-θ)` (Exercise 4.7, second part).
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.7 (first part)**. -/
theorem pauliX_mul_pauliY_mul_pauliX : pauliX * pauliY * pauliX = -pauliY := sorry

/-- **Nielsen & Chuang, Exercise 4.7 (second part)**: `X R_y(θ) X = R_y(-θ)`. -/
theorem pauliX_mul_rotY_mul_pauliX (θ : ℝ) : pauliX * rotY θ * pauliX = rotY (-θ) := by
  rw [rotY_eq, rotY_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, neg_div]

end AxQM.Concrete
