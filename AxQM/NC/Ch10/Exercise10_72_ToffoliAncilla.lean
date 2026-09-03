/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ToffoliAncilla
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.Composite
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.OneBitTeleportation
import AxQM.Basic.API.PauliYGate
import AxQM.NC.Ch10.Exercise10_67

/-!
# Nielsen & Chuang, Exercise 10.72 (fault-tolerant Toffoli ancilla state)

*(N&C p. 491.)*

Show how to fault-tolerantly prepare the Toffoli ancilla state (|000>+|010>+|100>+|111>)/2.

* `toffoliAncillaStabX1`
* `toffoliAncillaStabX2`
* `toffoliAncillaStabZ3`
* `toffoliAncillaStabX1_hasEigenstate_one`
* `toffoliAncillaStabX2_hasEigenstate_one`
* `toffoliAncillaStabZ3_hasEigenstate_one`
* `toffoliAncilla_eq_of_stabilized`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **First stabilizer generator** of the Toffoli ancilla, `g₁ = X₁ · CNOT₂₃`
(`X₁ = pauliXGate.onLeft (qubit ⊗ qubit)`, `CNOT₂₃ = cnotGate.onRight qubit`): the Toffoli conjugate
`C²(X)·X₁·C²(X)†` of the `|+⟩|+⟩|0⟩` stabilizer `X₁`, in explicit Pauli × controlled-`X` form
(Exercise 10.67, identity (a)). -/
def toffoliAncillaStabX1 : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit)

/-- **Second stabilizer generator** of the Toffoli ancilla, `g₂ = X₂ · CNOT₁₃` (`X₂ =
(pauliXGate.onLeft qubit).onRight qubit`, `CNOT₁₃ = cnotFirstThirdGate`). -/
def toffoliAncillaStabX2 : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate

/-- **Third stabilizer generator** of the Toffoli ancilla, `g₃ = Z₃ · CZ₁₂`
(`Z₃ = (pauliZGate.onRight qubit).onRight qubit`, `CZ₁₂ = controlledZLeftGate`): the Toffoli
conjugate `C²(X)·Z₃·C²(X)†` of the `|+⟩|+⟩|0⟩` stabilizer `Z₃`, in explicit Pauli × controlled-`Z`
form (Exercise 10.67, identity (b)). -/
def toffoliAncillaStabZ3 : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate

/-- **`g₁ = X₁·CNOT₂₃` stabilizes the Toffoli ancilla:** `g₁|Θ_T⟩ = |Θ_T⟩`. -/
theorem toffoliAncillaStabX1_hasEigenstate_one :
    toffoliAncillaStabX1.HasEigenstate 1 toffoliAncilla := sorry

/-- **`g₂ = X₂·CNOT₁₃` stabilizes the Toffoli ancilla:** `g₂|Θ_T⟩ = |Θ_T⟩`. -/
theorem toffoliAncillaStabX2_hasEigenstate_one :
    toffoliAncillaStabX2.HasEigenstate 1 toffoliAncilla := sorry

/-- **`g₃ = Z₃·CZ₁₂` stabilizes the Toffoli ancilla:** `g₃|Θ_T⟩ = |Θ_T⟩`. -/
theorem toffoliAncillaStabZ3_hasEigenstate_one :
    toffoliAncillaStabZ3.HasEigenstate 1 toffoliAncilla := sorry

/-! ### Completeness: the stabilizer group pins the ancilla

The three generators do not merely fix `|Θ_T⟩`; jointly they **determine** it. Measuring
`g₁, g₂, g₃` and post-selecting the all-`+1` outcome prepares *exactly* `|Θ_T⟩` (up to a global
phase) and nothing else — the *completeness* half of the stabilizer verification. -/

/-- **The stabilizer group pins the Toffoli ancilla (completeness).** Any pure state `ψ` fixed by
all three stabilizer generators `g₁ = X₁·CNOT₂₃`, `g₂ = X₂·CNOT₁₃`, `g₃ = Z₃·CZ₁₂` equals the
Toffoli ancilla `|Θ_T⟩` up to a global phase (`ψ.toState = toffoliAncilla.toState`). -/
theorem toffoliAncilla_eq_of_stabilized (ψ : PureState (qubit ⊗ (qubit ⊗ qubit)))
    (h1 : toffoliAncillaStabX1.HasEigenstate 1 ψ)
    (h2 : toffoliAncillaStabX2.HasEigenstate 1 ψ)
    (h3 : toffoliAncillaStabZ3.HasEigenstate 1 ψ) :
    ψ.toState = toffoliAncilla.toState := sorry

end AxQM
