/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.Rotation
import AxQM.Concrete.Hadamard

/-!
# Concrete: the ABC decomposition of the Hadamard gate (Nielsen & Chuang, Exercise 4.12)

Nielsen & Chuang, Exercise 4.12 asks to **give `A`, `B`, `C` and `α` for the Hadamard gate** in the
ABC decomposition of Corollary 4.2 (`U = e^{iα} A X B X C` with `A B C = I`).

## Main declarations
* `hadamardABC_A`, `hadamardABC_B`, `hadamardABC_C` — the explicit witnesses (the answer to
  "give `A`, `B`, `C`"), each a product of `§4.2` rotation matrices.
* `hadamardABC_A_mul_B_mul_C_eq_one` — `A B C = I` (Corollary 4.2's first relation).
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The Hadamard ABC witness `A = R_y(π/4)` (Nielsen & Chuang, Exercise 4.12). Corollary 4.2's
`A = R_z(β) R_y(γ/2)` with the Hadamard's Z–Y angles `β = 0`, `γ = π/2`. -/
noncomputable def hadamardABC_A : Matrix (Fin 2) (Fin 2) ℂ := rotY (Real.pi / 4)

/-- The Hadamard ABC witness `B = R_y(-π/4) R_z(-π/2)` (Nielsen & Chuang, Exercise 4.12).
Corollary 4.2's `B = R_y(-γ/2) R_z(-(δ+β)/2)` with `β = 0`, `γ = π/2`, `δ = π`. -/
noncomputable def hadamardABC_B : Matrix (Fin 2) (Fin 2) ℂ :=
  rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2))

/-- The Hadamard ABC witness `C = R_z(π/2)` (Nielsen & Chuang, Exercise 4.12). Corollary 4.2's
`C = R_z((δ-β)/2)` with `β = 0`, `δ = π`. -/
noncomputable def hadamardABC_C : Matrix (Fin 2) (Fin 2) ℂ := rotZ (Real.pi / 2)

/-- **Corollary 4.2's first relation for the Hadamard witnesses:** `A B C = I`. -/
theorem hadamardABC_A_mul_B_mul_C_eq_one :
    hadamardABC_A * hadamardABC_B * hadamardABC_C = 1 := sorry

end AxQM.Concrete
