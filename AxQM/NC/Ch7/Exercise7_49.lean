/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRSwap
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.NC.Ch4.Exercise4_17
import AxQM.NC.Ch7.Exercise7_41

/-!
# Nielsen & Chuang, Exercise 7.49 (NMR swap gate)

*(N&C p. 338.)*

NMR swap gate: construct a quantum circuit using e^{-iH/2ℏJ}, R_x, R_y to implement a swap
operation.

* `nmrSwapCircuit_evolve_eq_swap` — the physics reading (the channel): for `c·t = π/4`, the pure
  `R_x`/`R_y`/coupling circuit `NMRSwap.swapCircuit c t` induces the *same state channel* `ρ ↦ U ρ
  U†` as the `SWAP` gate, on every state.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.49 — the physics reading (channel equality).** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the circuit `NMRSwap.swapCircuit c t` — built from
**only** the coupling propagator `e^{-iH/2ℏJ}` and the `90°` rotations `R_x`, `R_y` — induces the
*same state
channel* `ρ ↦ U ρ U†` as the `SWAP` gate, on every state `ρ`. The overall global phase of the gate
identity is physically unobservable (it cancels in the conjugation), so this pulse sequence realises
a `SWAP` between the two coupled spins — the answer to the exercise. -/
theorem nmrSwapCircuit_evolve_eq_swap (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (NMRSwap.swapCircuit c t).evolve ρ = Evolution.swap.evolve ρ := sorry

end AxQM
