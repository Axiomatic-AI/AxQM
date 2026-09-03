/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliYGate
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.HadamardRotation

/-!
# Nielsen & Chuang, Exercise 4.31 (More circuit identities)

*(N&C p. 185.)*

Prove eight CNOT-conjugation circuit identities (CX1C=X1X2, etc.).

* `cnotGate_conj_pauliXGate_onLeft` — eq. (4.32): `C·X₁·C = X₁·X₂`.
* `cnotGate_conj_pauliYGate_onLeft` — eq. (4.33): `C·Y₁·C = Y₁·X₂`.
* `cnotGate_conj_pauliZGate_onLeft` — eq. (4.34): `C·Z₁·C = Z₁`.
* `cnotGate_conj_pauliXGate_onRight` — eq. (4.35): `C·X₂·C = X₂`.
* `cnotGate_conj_pauliYGate_onRight` — eq. (4.36): `C·Y₂·C = Z₁·Y₂`.
* `cnotGate_conj_pauliZGate_onRight` — eq. (4.37): `C·Z₂·C = Z₁·Z₂`.
* `rotZGate_onLeft_comm_cnotGate` — eq. (4.38): `R_{z,1}(θ)·C = C·R_{z,1}(θ)`.
* `rotXGate_onRight_comm_cnotGate` — eq. (4.39): `R_{x,2}(θ)·C = C·R_{x,2}(θ)`.
-/

noncomputable section

namespace AxQM

/-- **N&C eq. (4.32):** `C·X₁·C = X₁·X₂`. -/
theorem cnotGate_conj_pauliXGate_onLeft :
    cnotGate.comp ((pauliXGate.onLeft qubit).comp cnotGate)
      = (pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit) := sorry

/-- **N&C eq. (4.33):** `C·Y₁·C = Y₁·X₂`. -/
theorem cnotGate_conj_pauliYGate_onLeft :
    cnotGate.comp ((pauliYGate.onLeft qubit).comp cnotGate)
      = (pauliYGate.onLeft qubit).comp (pauliXGate.onRight qubit) := sorry

/-- **N&C eq. (4.34):** `C·Z₁·C = Z₁`. -/
theorem cnotGate_conj_pauliZGate_onLeft :
    cnotGate.comp ((pauliZGate.onLeft qubit).comp cnotGate) = pauliZGate.onLeft qubit := sorry

/-- **N&C eq. (4.35):** `C·X₂·C = X₂`. -/
theorem cnotGate_conj_pauliXGate_onRight :
    cnotGate.comp ((pauliXGate.onRight qubit).comp cnotGate) = pauliXGate.onRight qubit := sorry

/-- **N&C eq. (4.36):** `C·Y₂·C = Z₁·Y₂`. -/
theorem cnotGate_conj_pauliYGate_onRight :
    cnotGate.comp ((pauliYGate.onRight qubit).comp cnotGate)
      = (pauliZGate.onLeft qubit).comp (pauliYGate.onRight qubit) := sorry

/-- **N&C eq. (4.37):** `C·Z₂·C = Z₁·Z₂`. -/
theorem cnotGate_conj_pauliZGate_onRight :
    cnotGate.comp ((pauliZGate.onRight qubit).comp cnotGate)
      = (pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit) := sorry

/-- **N&C eq. (4.38):** `R_{z,1}(θ)·C = C·R_{z,1}(θ)`. -/
theorem rotZGate_onLeft_comm_cnotGate (θ : ℝ) :
    ((rotZGate θ).onLeft qubit).comp cnotGate
      = cnotGate.comp ((rotZGate θ).onLeft qubit) := sorry

/-- **N&C eq. (4.39):** `R_{x,2}(θ)·C = C·R_{x,2}(θ)`. An `x`-rotation on the target (qubit 2)
commutes with `CNOT`. -/
theorem rotXGate_onRight_comm_cnotGate (θ : ℝ) :
    ((rotXGate θ).onRight qubit).comp cnotGate
      = cnotGate.comp ((rotXGate θ).onRight qubit) := sorry

end AxQM
