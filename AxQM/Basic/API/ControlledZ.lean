/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.HadamardPauliConjugation

/-!
# AxQM.Basic.API — the controlled-`Z` gate

The operator-level form of Nielsen & Chuang's controlled-`Z` (controlled-phase) gate (N&C §4.3).

## Main declarations
* `controlledZGate = controlledUnitary pauliZGate` — the **controlled-`Z`** gate on `qubit ⊗ qubit`
  (N&C's `diag(1, 1, 1, -1)`): the `Evolution` `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` that applies the phase
  flip `Z` to the target exactly when the control qubit is `|1⟩`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The controlled-`Z` gate** on two qubits (Nielsen & Chuang §4.3), the controlled-`U` gate with
`U = Z`: it applies the phase flip `Z` to the target qubit exactly when the control qubit is `|1⟩`.
Its operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` is N&C's specifying matrix `diag(1, 1, 1, -1)` in the
computational basis. -/
def controlledZGate : Evolution (qubit ⊗ qubit) := controlledUnitary pauliZGate

end AxQM
