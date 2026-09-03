/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RzThreeFifthsCircuit
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.CascadedMeasurement
import AxQM.Basic.API.MeasureObservable

/-!
# AxQM.Basic.API — measuring both ancillas of the Figure 4.17 `R_z(θ)` circuit

The *two-ancilla measurement* of the Figure 4.17 `R_z(θ)` circuit of Nielsen & Chuang,
Exercise 4.41, as an explicit `Measurement`.

## Main declarations
* `rzTwoAncillaMeasurement` — the projective measurement of the **two ancilla qubits** of `qubit ⊗
  (qubit ⊗ qubit)` in the computational basis, leaving the target untouched.
-/

open scoped TensorProduct InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The two-ancilla measurement of the Figure 4.17 circuit.** Measuring both control (ancilla)
qubits of `qubit ⊗ (qubit ⊗ qubit)` in the computational basis, leaving the target untouched: the
cascade of `controlMeasurement (qubit ⊗ qubit)` (ancilla 1, the left factor) and
`(controlMeasurement qubit).onRight qubit` (ancilla 2, the left qubit of the right factor). Its
operator for outcome `(a', b')` is the two-ancilla projector `|a'⟩⟨a'| ⊗ (|b'⟩⟨b'| ⊗ 1)`. -/
def rzTwoAncillaMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ (qubit ⊗ qubit)) :=
  (controlMeasurement (qubit ⊗ qubit)).cascade ((controlMeasurement qubit).onRight qubit)

end AxQM
