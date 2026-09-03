/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PiEighthGate

/-!
# Nielsen & Chuang, Exercise 4.3 — up to a global phase, the π/8 gate satisfies `T = R_z(π/4)`

*(N&C p. 175.)*

Show that up to global phase the pi/8 gate satisfies T=R_z(pi/4).

* `tGate_evolve_eq_rotZGate_evolve` — for every state `ρ` of the qubit, `T.evolve ρ =
  R_z(π/4).evolve ρ`, i.e. the π/8 gate and `R_z(π/4)` induce the *same* state evolution.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.3.** Up to a global phase, the π/8 gate `T` equals `R_z(π/4)`:
as quantum operations they are the *same* gate — for every state `ρ` of the qubit, `T` and
`R_z(π/4)` induce the identical state evolution `ρ ↦ U ρ U†`. The global phase `e^{iπ/8}` relating
the two operators (eq. 4.3) has unit modulus, so it cancels in the conjugation defining
`Evolution.evolve`; this is the precise sense in which a global phase is physically
unobservable. -/
theorem tGate_evolve_eq_rotZGate_evolve (ρ : State qubit) :
    tGate.evolve ρ = (rotZGate (Real.pi / 4)).evolve ρ := sorry

end AxQM
