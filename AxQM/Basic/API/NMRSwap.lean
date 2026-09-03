/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRControlledZ
import AxQM.Basic.API.ControlledRotation
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.HadamardRyRx

/-!
# AxQM.Basic.API — the pure-`R_x`/`R_y` SWAP circuit

Machinery for **Nielsen & Chuang Exercise 7.49** (the NMR `SWAP` gate): build a `SWAP` using
**only** the coupling evolution `e^{-iH/2ℏJ}` and the `90°` rotations `R_x`, `R_y`, starting from
the three-`CNOT` circuit of Figure 1.7. The standard reductions produce Hadamards, `z`-rotations,
and controlled-`Z`s each realised only *up to a physically-irrelevant global phase* (N&C's own
words), so this file supplies the bookkeeping that makes those phases cancel automatically.
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

namespace NMRSwap

/-- **The Hadamard gate as an `R_x`/`R_y` pulse sequence**: `R_x(π) · R_y(π/2)`. -/
def hadamard : Evolution qubit := (rotXGate Real.pi).comp (rotYGate (Real.pi / 2))

/-- **The `z`-rotation from `R_x`, `R_y`:** `H · R_x(θ) · H` with the Hadamards `H` themselves
expanded to `R_x`/`R_y` pulses (`NMRSwap.hadamard`). Equals `rotZGate θ` up to a global phase. -/
def rotZ (θ : ℝ) : Evolution qubit := hadamard.comp ((rotXGate θ).comp hadamard)

/-- **The controlled-`Z` from coupling + `R_x`/`R_y`:** one period of `Z₁Z₂`-coupled evolution
`e^{-i c Z₁Z₂ t}` followed by the pure-`R_x`/`R_y` `z`-rotation `NMRSwap.rotZ (-π/2)` on each
spin — the Exercise 7.41 sequence with its `R_z` pulses expanded. -/
def controlledZ (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((couplingZZHamiltonian c).propagator 1 0 t).comp
    (((rotZ (-(Real.pi / 2))).onLeft qubit).comp ((rotZ (-(Real.pi / 2))).onRight qubit))

/-- **The `CNOT` from coupling + `R_x`/`R_y`:** `(1⊗H) · CZ · (1⊗H)`, with the
Hadamards and the controlled-`Z` realised from `R_x`, `R_y`, and the coupling (`NMRSwap.hadamard`,
`NMRSwap.controlledZ`). The two Hadamards act on the *target* (right) qubit. -/
def cnot (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (hadamard.onRight qubit).comp ((controlledZ c t).comp (hadamard.onRight qubit))

/-- **The reversed `CNOT` from coupling + `R_x`/`R_y`:** `(H⊗1) · CZ · (H⊗1)` — the `CNOT`
controlled on the second qubit, with the Hadamards on the *first* (target) qubit. -/
def reversedCnot (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (hadamard.onLeft qubit).comp ((controlledZ c t).comp (hadamard.onLeft qubit))

/-- **The NMR `SWAP` circuit**: the three-`CNOT` circuit of Figure 1.7, `CNOT · reversedCNOT ·
CNOT`, with every `CNOT` realised from the coupling and `R_x`, `R_y` only. -/
def swapCircuit (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (cnot c t).comp ((reversedCnot c t).comp (cnot c t))

end NMRSwap

end AxQM
