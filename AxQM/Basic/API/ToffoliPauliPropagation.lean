/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation

/-!
# AxQM.Basic.API — underlying operator support for Toffoli Pauli propagation

Building blocks for the Toffoli-gate error-propagation identities of Nielsen &
Chuang **Exercise 10.67** (the `X`/`Z` commutation rules used to move a Toffoli through Pauli
byproducts in the fault-tolerant π/8 and Toffoli constructions, Exercises 10.66–10.68).

## Main declarations
* `controlledZLeftGate = C(Z ⊗ 1)` — the controlled-`Z` on qubits 1, 2 (control qubit 1, phase `Z`
  on qubit 2), qubit 3 untouched. Mirrors `cnotLeftGate`, the `CNOT` on the same left pair.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Controlled-`Z` on qubits 1, 2 with control qubit 1**, `|q₁, q₂, q₃⟩ ↦ (-1)^{q₁q₂}|q₁, q₂,
q₃⟩`. Since the control is qubit 1 this needs no re-bracketing. -/
def controlledZLeftGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (pauliZGate.onLeft qubit)

end AxQM
