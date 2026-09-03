/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGate
import AxQM.Concrete.RotationDecompositionXY

/-!
# Concrete: the π/8 (T) gate conjugated by Hadamard (Nielsen & Chuang, Exercise 4.14)

Nielsen & Chuang, Exercise 4.14 asks to show that, **up to a global phase**, `H T H = R_x(π/4)`,
where `T` is the π/8 gate (eq. 4.2) and `R_x` the `x̂`-axis rotation (eq. 4.4).

## Main declarations
* `hadamardC_mul_tMatrix_mul_hadamardC` — **Exercise 4.14 itself**:
  `H T H = e^{iπ/8} • R_x(π/4)`, i.e. `H T H` equals `R_x(π/4)` up to the unit-modulus global
  phase `e^{iπ/8}`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.14.** Up to a global phase, the π/8 (T) gate conjugated by the
Hadamard gate is the `x̂`-rotation by `π/4`: `H T H = e^{iπ/8} • R_x(π/4)`. The scalar
`e^{iπ/8}` has modulus `1`, so it is an (unobservable) global phase. -/
theorem hadamardC_mul_tMatrix_mul_hadamardC :
    hadamardC * tMatrix * hadamardC
      = Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) • rotX (Real.pi / 4) := sorry

end AxQM.Concrete
