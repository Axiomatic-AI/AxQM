/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.ControlledRotation
import AxQM.Basic.API.Teleportation
import AxQM.Concrete.Rotation

/-!
# AxQM.Basic.API — the relative-phase Toffoli circuit

Infrastructure for **Nielsen & Chuang, Exercise 4.26**: the three-qubit circuit made
of four `R_y(±π/4)` rotations on the target qubit interleaved with three `CNOT`s (two controlled by
the second qubit, one by the first) that implements a Toffoli gate *up to relative phases*.

## Main declarations
* `relativePhaseToffoliGate` — the circuit of Exercise 4.26 as an `Evolution` on
  `qubit ⊗ (qubit ⊗ qubit)`: reading left to right on the target (third) qubit,
  `R_y(π/4) · CNOT₂₃ · R_y(π/4) · CNOT₁₃ · R_y(-π/4) · CNOT₂₃ · R_y(-π/4)`, where `CNOT₂₃` is the
  `CNOT` with control qubit 2 and `CNOT₁₃` the one with control qubit 1, both targeting qubit 3.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **`X` is an involution:** `X · X = 1` as a gate. -/
theorem pauliXGate_comp_pauliXGate : pauliXGate.comp pauliXGate = Evolution.id := by
  have h : pauliXGate.comp pauliXGate = pauliXGate.comp ((rotYGate 0).comp pauliXGate) := by
    rw [rotYGate_zero, Evolution.id_comp]
  rw [h, pauliXGate_comp_rotYGate_comp_pauliXGate, neg_zero, rotYGate_zero]

/-- **`R_y(θ)` on the target (third) qubit** of `qubit ⊗ (qubit ⊗ qubit)`: `1 ⊗ (1 ⊗ R_y θ)`. -/
def rotYThirdGate (θ : ℝ) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((rotYGate θ).onRight qubit).onRight qubit

/-- **`CNOT` with control qubit 1 and target qubit 3**, `C(1 ⊗ X)`: fires `X` on the third qubit
when the first (control) qubit is `|1⟩`, leaving the second qubit untouched. -/
def cnotFirstThirdGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (pauliXGate.onRight qubit)

/-- **The relative-phase Toffoli circuit of Nielsen & Chuang, Exercise 4.26.** On `qubit ⊗ (qubit ⊗
qubit)`, reading left to right on the target (third) qubit. -/
def relativePhaseToffoliGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (rotYThirdGate (-(Real.pi / 4))).comp ((cnotGate.onRight qubit).comp
    ((rotYThirdGate (-(Real.pi / 4))).comp (cnotFirstThirdGate.comp
      ((rotYThirdGate (Real.pi / 4)).comp ((cnotGate.onRight qubit).comp
        (rotYThirdGate (Real.pi / 4)))))))

end AxQM
