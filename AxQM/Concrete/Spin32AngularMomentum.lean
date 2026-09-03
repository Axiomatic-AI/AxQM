/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Concrete: the spin-3/2 angular-momentum operators (Nielsen & Chuang, Exercise 7.28, part 1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.28 (p. 315) — the
"hyperfine states" exercise — introduces, for a **spin-3/2** particle (nuclear spin `I = 3/2`),
the three angular-momentum operators as explicit `4 × 4` matrices (equations (7.106)–(7.108)).

## Contents

* `sqrt3` — the constant `√3 : ℂ`.
* `spin32Ix`, `spin32Iy`, `spin32Iz` — the three operators as `4 × 4` matrices, from
  (7.106)–(7.108).
* `spin32_comm_ix_iy`, `spin32_comm_iy_iz`, `spin32_comm_iz_ix` — **part 1 of the exercise**: the
  three cyclic `SU(2)` commutation relations `[i_x, i_y] = i·i_z`, `[i_y, i_z] = i·i_x`,
  `[i_z, i_x] = i·i_y`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The real square root `√3`, as a complex number. -/
noncomputable def sqrt3 : ℂ := (Real.sqrt 3 : ℂ)

/-- The spin-3/2 angular-momentum `x`-operator `i_x` as a `4 × 4` matrix
(Nielsen & Chuang (7.106)): `i_x = ½·!![0,√3,0,0; √3,0,2,0; 0,2,0,√3; 0,0,√3,0]`. -/
noncomputable def spin32Ix : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![0, sqrt3, 0, 0; sqrt3, 0, 2, 0; 0, 2, 0, sqrt3; 0, 0, sqrt3, 0]

/-- The spin-3/2 angular-momentum `y`-operator `i_y` as a `4 × 4` matrix
(Nielsen & Chuang (7.107)): `i_y = ½·!![0,i√3,0,0; -i√3,0,2i,0; 0,-2i,0,i√3; 0,0,-i√3,0]`. -/
noncomputable def spin32Iy : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![0, sqrt3 * I, 0, 0; -(sqrt3 * I), 0, 2 * I, 0;
                 0, -(2 * I), 0, sqrt3 * I; 0, 0, -(sqrt3 * I), 0]

/-- The spin-3/2 angular-momentum `z`-operator `i_z` as a `4 × 4` matrix
(Nielsen & Chuang (7.108)): the diagonal matrix `i_z = ½·diag(-3, -1, 1, 3)`, so the basis is
ordered by increasing `m_I = (-3/2, -1/2, 1/2, 3/2)`. -/
noncomputable def spin32Iz : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![-3, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 3]

/-- `[i_x, i_y] = i·i_z`: the first cyclic `SU(2)` commutation relation for the spin-3/2 operators
(Nielsen & Chuang, Exercise 7.28, part 1). -/
theorem spin32_comm_ix_iy :
    spin32Ix * spin32Iy - spin32Iy * spin32Ix = I • spin32Iz := sorry

/-- `[i_y, i_z] = i·i_x`: the second cyclic `SU(2)` commutation relation for the spin-3/2
operators (Nielsen & Chuang, Exercise 7.28, part 1). -/
theorem spin32_comm_iy_iz :
    spin32Iy * spin32Iz - spin32Iz * spin32Iy = I • spin32Ix := sorry

/-- `[i_z, i_x] = i·i_y`: the third cyclic `SU(2)` commutation relation for the spin-3/2 operators
(Nielsen & Chuang, Exercise 7.28, part 1). -/
theorem spin32_comm_iz_ix :
    spin32Iz * spin32Ix - spin32Ix * spin32Iz = I • spin32Iy := sorry

end AxQM.Concrete
