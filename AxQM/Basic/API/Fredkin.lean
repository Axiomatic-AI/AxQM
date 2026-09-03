/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.Swap

/-!
# AxQM.Basic.API — the Fredkin (controlled-`SWAP`) gate and its construction gates

Infrastructure for Nielsen & Chuang **Exercise 4.25** (Fredkin gate construction):
the controlled-`SWAP` gate `fredkinGate` together with the two auxiliary gates its three-Toffoli
construction is built from — a reversed `CNOT` and the "middle" Toffoli (controls on qubits 1 and
3, target qubit 2).

## Main declarations
* `fredkinGate` — the **Fredkin gate** `C(SWAP)` on `qubit ⊗ (qubit ⊗ qubit)`: the single-qubit
  controlled gate `controlledUnitary` applied to the two-qubit `SWAP`, i.e. it swaps qubits 2 and 3
  exactly when the control qubit 1 is `|1⟩`. This is precisely the transform of N&C eq. (4.30).
* `reversedCnotGate` — `CNOT` with the roles of the two qubits interchanged (control on the second
  qubit, target on the first), realised as the swap-conjugate `SWAP · CNOT · SWAP`; its truth table
  is `|a, b⟩ ↦ |a ⊕ b, b⟩`.
* `middleToffoliGate` — the doubly-controlled `X` with controls on qubits 1 and 3 and target
  qubit 2, `C(reversedCNOT)`; its truth table is `|c, a, b⟩ ↦ |c, a ⊕ c·b, b⟩`. This is the middle
  gate of the swap construction — a Toffoli whose target is qubit 2 rather than qubit 3.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Fredkin gate** `C(SWAP)` (Nielsen & Chuang §1.3.4, eq. 4.30): the `Evolution` on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)` that swaps the last two (target) qubits exactly when
the first (control) qubit is `|1⟩`. It is the single-qubit-controlled gate `controlledUnitary`
applied to the two-qubit `SWAP`, so it is a genuine unitary `Evolution` with no new obligation. -/
def fredkinGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (Evolution.swap (S := qubit))

/-- **The reversed `CNOT`**: the controlled-`NOT` with control on the *second* qubit and target on
the *first*, obtained by conjugating `cnotGate` with the factor swap, `reversedCNOT = SWAP ·
CNOT · SWAP`. -/
def reversedCnotGate : Evolution (qubit ⊗ qubit) :=
  (Evolution.swap (S := qubit)).comp (cnotGate.comp (Evolution.swap (S := qubit)))

/-- **The middle Toffoli** of the Fredkin swap construction: the doubly-controlled `X` with controls
on qubits 1 and 3 and target qubit 2, realised as `C(reversedCNOT)`. -/
def middleToffoliGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary reversedCnotGate

end AxQM
