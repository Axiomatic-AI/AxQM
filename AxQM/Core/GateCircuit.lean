/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary

/-!
# A typed gate-count model for three-qubit circuits (Nielsen & Chuang §4.3)

Nielsen & Chuang's controlled-operation exercises make **gate-count** claims — a `C²(U)` gate from
at most eight one-qubit gates and six CNOTs, a reduction from three single-qubit gates to two, and
so on. This file defines a typed
**circuit** on the three-qubit system `qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`) as a `List` of
`Gate3`s, each either a one-qubit gate on a chosen wire or a CNOT on a chosen control/target pair,
together with the two occurrence counts.

## Main declarations
* `Gate3` — a gate on `qubit ⊗ (qubit ⊗ qubit)`: `oneQubit (wire) (g)` or `cnot (control) (target)`.
* `Gate3.onWire` / `Gate3.cnotOn` — the `Evolution` embeddings of the two gate kinds; `Gate3.denote`
  packages them. `gateCircuit gs = (gs.map Gate3.denote).prod` composes a whole list.
* `oneQubitCount` / `cnotCount` — the two `List.countP` occurrence counts.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A gate in a three-qubit circuit** on `qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`): either a
one-qubit gate `g` on a chosen `wire`, or a `CNOT` with a chosen `control` and `target` wire. -/
inductive Gate3 where
  | /-- A one-qubit gate `g` acting on the wire `wire ∈ {0, 1, 2}`. -/
    oneQubit (wire : Fin 3) (g : Evolution qubit)
  | /-- A `CNOT` gate with control wire `control` and target wire `target`. -/
    cnot (control target : Fin 3)

namespace Gate3

/-- **A one-qubit gate on a chosen wire** of `qubit ⊗ (qubit ⊗ qubit)`. -/
def onWire : Fin 3 → Evolution qubit → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | 0, g => g.onLeft (qubit ⊗ qubit)
  | 1, g => (g.onLeft qubit).onRight qubit
  | _, g => (g.onRight qubit).onRight qubit

/-- **A CNOT on a chosen control/target pair** of `qubit ⊗ (qubit ⊗ qubit)`. The three pairs that
occur in Chapter 4 are realised without a SWAP. Every other pair (reversed or diagonal — unused)
is sent to the identity `1`. -/
def cnotOn : Fin 3 → Fin 3 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | 0, 1 => controlledUnitary (pauliXGate.onLeft qubit)
  | 0, 2 => controlledUnitary (pauliXGate.onRight qubit)
  | 1, 2 => cnotGate.onRight qubit
  | _, _ => 1

/-- **The `Evolution` denoted by a single gate**: the wire embedding of a one-qubit gate, or the
control/target embedding of a CNOT. -/
def denote : Gate3 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | oneQubit w g => onWire w g
  | cnot c t => cnotOn c t

/-- Whether a gate is a one-qubit gate. -/
def isOneQubit : Gate3 → Bool
  | oneQubit .. => true
  | cnot .. => false

/-- Whether a gate is a CNOT gate. -/
def isCnot : Gate3 → Bool
  | oneQubit .. => false
  | cnot .. => true

end Gate3

/-- **The evolution implemented by a gate list**. -/
def gateCircuit (gs : List Gate3) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (gs.map Gate3.denote).prod

/-- **The number of one-qubit gates** in a circuit. -/
def oneQubitCount (gs : List Gate3) : ℕ := gs.countP Gate3.isOneQubit

/-- **The number of CNOT gates** in a circuit. -/
def cnotCount (gs : List Gate3) : ℕ := gs.countP Gate3.isCnot

end AxQM
