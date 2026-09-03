/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.ControlledUnitary

/-!
# Nielsen & Chuang, Exercise 4.24 (Figure 4.9 implements the Toffoli gate)

*(N&C p. 182.)*

Verify Figure 4.9 implements the Toffoli gate from H,S,CNOT,T gates.

* `figure49TargetBlock` — the eight `CNOT`/`T`/`T†` gates of Figure 4.9 that lie between the two
  target-wire `Hadamard`s (the block `Q` conjugated by `H₃`).
* `figure49ControlBlock` — the six `CNOT`/`T†`/`T`/`S` gates of Figure 4.9 that come after the
  second `Hadamard`, all on the two control wires (the block `P`).
* `toffoliFig49Circuit` — the full Figure 4.9 circuit, `P · H₃ · Q · H₃`.
* `toffoliFig49Circuit_eq_toffoliGate` — the exercise: `toffoliFig49Circuit = toffoliGate`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The target-wire block of Figure 4.9** (`Q`): the eight gates between the two `Hadamard`s on
the target `q₃`, reading Figure 4.9 left to right (earliest gate innermost) —
`CNOT₂₃, T†₃, CNOT₁₃, T₃, CNOT₂₃, T†₃, CNOT₁₃, T₃`. -/
def figure49TargetBlock : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (((phaseShiftGate (Real.pi / 4)).onRight qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onRight qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onRight qubit).onRight qubit).comp
  ((cnotGate.onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onRight qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onRight qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onRight qubit).onRight qubit).comp
  (cnotGate.onRight qubit)))))))

/-- **The control-wire block of Figure 4.9** (`P`): the six gates after the second `Hadamard`, all
on the control wires `q₁, q₂`, reading Figure 4.9 left to right (earliest gate innermost) —
`T†₂, CNOT₁₂, T†₂, CNOT₁₂, T₁, S₂`. -/
def figure49ControlBlock : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (((phaseShiftGate (Real.pi / 2)).onLeft qubit).onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onLeft (qubit ⊗ qubit))).comp
  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
  (((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit)))))

/-- **The full Figure 4.9 circuit** implementing the Toffoli gate (Nielsen & Chuang §4.3), on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)` (`q₁ ⊗ (q₂ ⊗ q₃)`). It is `P · H₃ · Q · H₃`: the target
block `figure49TargetBlock` (`Q`) is conjugated by the target `Hadamard`
`H₃ = (hadamardGate.onRight qubit).onRight qubit`, then the control block `figure49ControlBlock`
(`P`) is applied. Reading right to left (the innermost `comp` acts first): initial `H₃`, target
block, second `H₃`, control block. -/
def toffoliFig49Circuit : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  figure49ControlBlock.comp
    (((hadamardGate.onRight qubit).onRight qubit).comp
      (figure49TargetBlock.comp ((hadamardGate.onRight qubit).onRight qubit)))

/-- **Nielsen & Chuang, Exercise 4.24: Figure 4.9 implements the Toffoli gate.** The full Figure 4.9
circuit equals the Toffoli gate `C²(X)`: `toffoliFig49Circuit = toffoliGate`.
-/
theorem toffoliFig49Circuit_eq_toffoliGate : toffoliFig49Circuit = toffoliGate := sorry

end AxQM
