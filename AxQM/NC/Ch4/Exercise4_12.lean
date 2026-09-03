/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardABC

/-!
# Nielsen & Chuang, Exercise 4.12 — `A`, `B`, `C`, `α` for the Hadamard gate

*(N&C p. 176.)*

Give A,B,C and alpha for the Hadamard gate in the ABC decomposition.

* `hadamardGate_evolve_eq_hadamardABCGate_evolve` — for every state `ρ` of the qubit, `H.evolve ρ =
  (A X B X C).evolve ρ`, i.e. the Hadamard gate and its ABC gate product induce the *same* state
  evolution `ρ ↦ U ρ U†`, where `A = R_y(π/4)`, `B = R_y(-π/4) R_z(-π/2)`, `C = R_z(π/2)`, `X =
  pauliXGate`.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.12.** The ABC decomposition of the Hadamard gate: with `α = π/2`,
`A = R_y(π/4)`, `B = R_y(-π/4) R_z(-π/2)`, `C = R_z(π/2)`, the Hadamard gate `H` equals its ABC
gate product `A X B X C` *as a quantum operation* — for every state `ρ` of the qubit, `H` and
the product induce the identical state evolution `ρ ↦ U ρ U†`. -/
theorem hadamardGate_evolve_eq_hadamardABCGate_evolve (ρ : State qubit) :
    hadamardGate.evolve ρ
      = (((((rotYGate (Real.pi / 4)).comp pauliXGate).comp
          ((rotYGate (-(Real.pi / 4))).comp (rotZGate (-(Real.pi / 2))))).comp pauliXGate).comp
          (rotZGate (Real.pi / 2))).evolve ρ := sorry

end AxQM
