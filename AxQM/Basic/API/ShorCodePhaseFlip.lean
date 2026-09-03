/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodeBlock
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation

/-!
# AxQM.Basic.API — block-level phase-flip gates

Infrastructure for the phase-flip errors and the recovery operator of one Shor-code
block (Nielsen & Chuang §10.2, Exercises 10.5–10.6). A block is the three-qubit register
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` carrying a cat state `catBlockVec σ = |000⟩ + (−1)^σ |111⟩`.
Here we treat the Pauli `Z`s as **unitary gates**
(`Evolution`s), the operational form a phase-flip *error* and its *recovery* both take.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The phase-flip gate `Z` on the `i`-th qubit of a block** (`i : Fin 3`), on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: `Z ⊗ I ⊗ I`, `I ⊗ Z ⊗ I`, `I ⊗ I ⊗ Z` for `i = 0, 1, 2`.
It models a phase-flip error on one of the block's three physical qubits. -/
def blockPhaseFlip : Fin 3 → Evolution bitFlipReg
  | 0 => pauliZGate ⊗ ((Evolution.id : Evolution qubit) ⊗ (Evolution.id : Evolution qubit))
  | 1 => (Evolution.id : Evolution qubit) ⊗ (pauliZGate ⊗ (Evolution.id : Evolution qubit))
  | 2 => (Evolution.id : Evolution qubit) ⊗ ((Evolution.id : Evolution qubit) ⊗ pauliZGate)

/-- **The recovery gate `Z ⊗ Z ⊗ Z = Z₁Z₂Z₃`** on a block: N&C's phase-flip recovery
operator. -/
def blockZGate : Evolution bitFlipReg :=
  pauliZGate ⊗ (pauliZGate ⊗ pauliZGate)

end AxQM
