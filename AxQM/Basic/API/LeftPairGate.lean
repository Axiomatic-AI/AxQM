/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm

/-!
# AxQM.Basic.API — CNOT / reversed-CNOT on the *left pair* of three qubits

Infrastructure supplying the two `CNOT` placements that act on qubits **1 and 2** of
the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)`, leaving qubit 3 untouched. The
existing gate vocabulary (`cnotGate.onRight`, `reversedCnotGate.onRight`, `toffoliGate`,
`middleToffoliGate`) only reaches qubits 2 and 3, or uses qubit 1 as a *control*; nothing flips
qubit 1. These two gates fill that gap and are reused by any circuit that must act on the first
qubit as a target (e.g. N&C Exercise 4.27's partial cyclic permutation).

## Main declarations
* `cnotLeftGate` — the `CNOT` with control qubit 1 and target qubit 2 (`|q₁,q₂,q₃⟩ ↦
  |q₁, q₂⊕q₁, q₃⟩`), realised as `C(X ⊗ 1)` (a single-qubit-controlled gate, so no re-bracketing is
  needed).
* `reversedCnotLeftGate` — the `CNOT` with control qubit 2 and target qubit 1 (`|q₁,q₂,q₃⟩ ↦
  |q₁⊕q₂, q₂, q₃⟩`). Its target is qubit 1, unreachable by the controlled-gate constructors, so it
  is the two-qubit `reversedCnotGate` placed on the left pair `(qubit ⊗ qubit) ⊗ qubit` via
  `onLeft` and transported to the right-associated system by the associator.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **`CNOT` on qubits 1, 2 with control qubit 1**, `|q₁, q₂, q₃⟩ ↦ |q₁, q₂ ⊕ q₁, q₃⟩`: the
single-qubit-controlled gate `C(X ⊗ 1)` flipping qubit 2 exactly when qubit 1 is `|1⟩`, qubit 3
untouched. Since the control is qubit 1 this needs no re-bracketing. -/
def cnotLeftGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (pauliXGate.onLeft qubit)

/-- **`CNOT` on qubits 1, 2 with control qubit 2**, `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂, q₂, q₃⟩`: the
two-qubit `reversedCnotGate` (control second, target first) placed on the left pair
`(qubit ⊗ qubit) ⊗ qubit` and transported to the right-associated three-qubit system by the
associator. Its target is qubit 1, unreachable by the controlled-gate constructors. -/
def reversedCnotLeftGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (reversedCnotGate.onLeft qubit).congr (QSystem.assoc qubit qubit qubit).symm

end AxQM
