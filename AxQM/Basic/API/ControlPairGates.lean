/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.LeftPairGate
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ

/-!
# AxQM.Basic.API — arbitrary two-qubit gates on the *control pairs* of three qubits

Infrastructure placing an **arbitrary** two-qubit `Evolution (qubit ⊗ qubit)` on the
two wire pairs of the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)` that involve
the first (control) qubit:

## Main declarations
* `leftPairGate U` / `outerPairGate U` — the two placements, realised by carrying the left/right
  factor embedding of `U` across the appropriate structural system isomorphism (`QSystem.assoc` for
  the left pair, `QSystem.Iso.leftComm` for the outer pair) with `Evolution.congr`, exactly as
  `reversedCnotLeftGate` does for its special case.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **An arbitrary two-qubit gate on qubits 1, 2** (wires `{0,1}`) of the right-associated
three-qubit system, qubit 3 untouched. -/
def leftPairGate (U : Evolution (qubit ⊗ qubit)) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (U.onLeft qubit).congr (QSystem.assoc qubit qubit qubit).symm

/-- **An arbitrary two-qubit gate on the outer qubits 1, 3** (wires `{0,2}`) of the right-associated
three-qubit system, qubit 2 untouched. Concretely `U` acts on qubits 1 and 3, qubit 2 idle. -/
def outerPairGate (U : Evolution (qubit ⊗ qubit)) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (U.onRight qubit).congr (QSystem.Iso.leftComm qubit qubit qubit).symm

end AxQM
