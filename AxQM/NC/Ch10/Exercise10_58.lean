/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.MeasureObservableAncilla
import AxQM.Basic.API.Teleportation
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 10.58 (Verifying the operator-measurement circuits)

*(N&C p. 474.)*

Verify circuits of Figs 10.13-10.15 measure operator M / X / Z, and the claimed equivalences.

* `measureObservableCircuit_pauliZGate_eq_reversedCnotGate` — Figure 10.15: the `Z`-measurement
  circuit `(H ⊗ 1) · C(Z) · (H ⊗ 1)` *equals* the reversed CNOT `reversedCnotGate` (control on the
  data qubit) — the "useful simplification" replacing the two Hadamards and a controlled-`Z` by a
  single controlled-`NOT` into the ancilla.
* `measureObservableCircuit_pauliXGate_eq_hadamardConjReversedCnot` — Figure 10.14: the
  `X`-measurement circuit `(H ⊗ 1) · C(X) · (H ⊗ 1)` *equals* the reversed CNOT conjugated by
  Hadamards on the data qubit, `(1 ⊗ H) · reversedCNOT · (1 ⊗ H)` — the "useful equivalent circuit".
* `measureObservableCircuit_pauliZGate_evolvePure_ketZero_qubitBasisZero`
* `measureObservableCircuit_pauliZGate_evolvePure_ketZero_qubitBasisOne`
* `measureObservableCircuit_pauliXGate_evolvePure_ketZero_qubitPlus`
* `measureObservableCircuit_pauliXGate_evolvePure_ketZero_qubitMinus`
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-! ### Figure 10.15: the `Z`-measurement equivalence -/

/-- **Nielsen & Chuang, Figure 10.15 (circuit equivalence).** The `Z`-measurement circuit
`(H ⊗ 1) · C(Z) · (H ⊗ 1)` equals the reversed CNOT (control on the data qubit) — the "useful
simplification": measuring `Z` needs no Hadamards, just a single controlled-`NOT` into the
ancilla. -/
theorem measureObservableCircuit_pauliZGate_eq_reversedCnotGate :
    measureObservableCircuit pauliZGate = reversedCnotGate := sorry

/-! ### Figure 10.14: the `X`-measurement equivalence -/

/-- **Nielsen & Chuang, Figure 10.14 (circuit equivalence).** The `X`-measurement circuit `(H ⊗ 1) ·
C(X) · (H ⊗ 1)` equals the reversed CNOT conjugated by Hadamards on the *data* qubit, `(1 ⊗ H) ·
reversedCNOT · (1 ⊗ H)` — the "useful equivalent circuit": flip to the `X`-eigenbasis on the
data qubit, do the data-controlled `NOT` into the ancilla, and flip back. -/
theorem measureObservableCircuit_pauliXGate_eq_hadamardConjReversedCnot :
    measureObservableCircuit pauliXGate
      = (hadamardGate.onRight qubit).comp (reversedCnotGate.comp (hadamardGate.onRight qubit)) :=
        sorry

/-! ### The `Z`-measurement circuit measures `Z` -/

/-- **Figure 10.15 measures `Z`, outcome `+1`.** On the `+1` eigenstate `|0⟩`, the `Z`-measurement
circuit sends `|0⟩ ⊗ |0⟩` to `|0⟩ ⊗ |0⟩`: the ancilla reads `0` (eigenvalue `+1`) with certainty and
the target is left in `|0⟩`. -/
theorem measureObservableCircuit_pauliZGate_evolvePure_ketZero_qubitBasisZero :
    (measureObservableCircuit pauliZGate).evolvePure ((qubitBasis 0) ⊗ (qubitBasis 0))
      = (qubitBasis 0) ⊗ (qubitBasis 0) := sorry

/-- **Figure 10.15 measures `Z`, outcome `-1`.** On the `-1` eigenstate `|1⟩`, the `Z`-measurement
circuit sends `|0⟩ ⊗ |1⟩` to `|1⟩ ⊗ |1⟩`: the ancilla reads `1` (eigenvalue `-1`) with certainty and
the target is left in `|1⟩`. -/
theorem measureObservableCircuit_pauliZGate_evolvePure_ketZero_qubitBasisOne :
    (measureObservableCircuit pauliZGate).evolvePure ((qubitBasis 0) ⊗ (qubitBasis 1))
      = (qubitBasis 1) ⊗ (qubitBasis 1) := sorry

/-! ### The `X`-measurement circuit measures `X` -/

/-- **Figure 10.14 measures `X`, outcome `+1`.** On the `+1` eigenstate `|+⟩`, the `X`-measurement
circuit sends `|0⟩ ⊗ |+⟩` to `|0⟩ ⊗ |+⟩`: the ancilla reads `0` (eigenvalue `+1`) with certainty and
the target is left in `|+⟩`. -/
theorem measureObservableCircuit_pauliXGate_evolvePure_ketZero_qubitPlus :
    (measureObservableCircuit pauliXGate).evolvePure ((qubitBasis 0) ⊗ qubitPlus)
      = (qubitBasis 0) ⊗ qubitPlus := sorry

/-- **Figure 10.14 measures `X`, outcome `-1`.** On the `-1` eigenstate `|-⟩`, the `X`-measurement
circuit sends `|0⟩ ⊗ |-⟩` to `|1⟩ ⊗ |-⟩`: the ancilla reads `1` (eigenvalue `-1`) with certainty and
the target is left in `|-⟩`. -/
theorem measureObservableCircuit_pauliXGate_evolvePure_ketZero_qubitMinus :
    (measureObservableCircuit pauliXGate).evolvePure ((qubitBasis 0) ⊗ qubitMinus)
      = (qubitBasis 1) ⊗ qubitMinus := sorry

end AxQM
