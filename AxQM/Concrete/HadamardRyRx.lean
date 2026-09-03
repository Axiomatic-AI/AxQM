/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import AxQM.Concrete.Hadamard

/-!
# Concrete: the Hadamard matrix from `R_y` and `R_x` rotations (Nielsen & Chuang, Ex. 7.31)

Nielsen & Chuang, Exercise 7.31 (§7.6.3, ion-trap single-qubit operations, p. 319) asks to
*construct a Hadamard gate from `R_y` and `R_x` rotations*. In that section the available
single-qubit primitives are the coordinate rotations `R_x(θ) = exp(−iθX/2)` and
`R_y(θ) = exp(−iθY/2)` (there written `exp(−iθS_x)`, `exp(−iθS_y)` with the spin operators
`S_x = X/2`, `S_y = Y/2`), and — by Theorem 4.1 — these generate every single-qubit operation up to
a global phase.

## Main declarations
* `hadamardC_eq_expPiDivTwo_smul_rotX_rotY` — **Exercise 7.31 as a matrix identity**: `H = e^{iπ/2}
  • (R_x(π) R_y(π/2))`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 7.31 (matrix form).** The Hadamard matrix is the `R_x`–`R_y`
rotation product up to the global phase `e^{iπ/2}`:
`H = e^{iπ/2} • (R_x(π) R_y(π/2))`. -/
theorem hadamardC_eq_expPiDivTwo_smul_rotX_rotY :
    hadamardC = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (rotX Real.pi * rotY (Real.pi / 2)) := sorry

end AxQM.Concrete
