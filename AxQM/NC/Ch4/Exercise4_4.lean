/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardRotation

/-!
# Nielsen & Chuang, Exercise 4.4 — the Hadamard gate as a product of `R_x`, `R_z` rotations

*(N&C p. 175.)*

Express Hadamard H as a product of R_x, R_z rotations and a phase e^{i phi}.

* `hadamardGate_evolve_eq_rotXGate_rotZGate_rotXGate_evolve` — for every state `ρ` of the qubit,
  `H.evolve ρ = (R_x(π/2) R_z(π/2) R_x(π/2)).evolve ρ`, i.e. the Hadamard gate and the `X`–`Z`–`X`
  rotation product induce the *same* state evolution.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.4.** Up to a global phase, the Hadamard gate `H` equals the
`X`–`Z`–`X` rotation product `R_x(π/2) R_z(π/2) R_x(π/2)`: as quantum operations they are the *same*
gate — for every state `ρ` of the qubit, `H` and the rotation product induce the identical state
evolution `ρ ↦ U ρ U†`. The two operators differ by a global phase of unit modulus, which is
physically unobservable — the sense in which Exercise 4.4's `e^{iϕ}` does not appear in the
statement. -/
theorem hadamardGate_evolve_eq_rotXGate_rotZGate_rotXGate_evolve (ρ : State qubit) :
    hadamardGate.evolve ρ
      = (((rotXGate (Real.pi / 2)).comp (rotZGate (Real.pi / 2))).comp
          (rotXGate (Real.pi / 2))).evolve ρ := sorry

end AxQM
