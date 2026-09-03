/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ControlledPowerSequence
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate

/-!
# The phase-estimation Hadamard layer (N&C §5.2, Figure 5.2) — the circuit's input-preparation gate

The first gate of the phase-estimation circuit (N&C Figure 5.2) is a **Hadamard layer**: a Hadamard
applied to each of the `t` control qubits, leaving the target register `S` untouched. Run on the
computational input `|0…0⟩ ⊗ |u⟩` it prepares the equal superposition `(1/√2ᵗ) ∑_b |b⟩ ⊗ |u⟩` over
all `2ᵗ` control registers.

## Main declarations
* `qtowerHadamardLayer t` — the **Hadamard layer** as an `Evolution` on `qtower t S`: a Hadamard on
  each control wire, identity on the target.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The phase-estimation Hadamard layer** as an `Evolution` on `qtower t S`: a Hadamard on each of
the `t` control wires, identity on the target register `S`. The first gate of N&C Figure 5.2,
generalised over an arbitrary target `S`. -/
def qtowerHadamardLayer : (t : ℕ) → Evolution (qtower t S)
  | 0 => Evolution.id
  | (t + 1) => (hadamardGate.onLeft (qtower t S)).comp ((qtowerHadamardLayer t).onRight qubit)

end AxQM
