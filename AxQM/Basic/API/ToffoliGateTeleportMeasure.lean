/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ToffoliGateTeleportReshape
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.RzThreeFifthsCircuit
import AxQM.Basic.API.GateTeleportMeasurement
import AxQM.Basic.API.BellLocalMeasurement

/-!
# AxQM.Basic.API — the three data-qubit measurements of Toffoli gate teleportation

The **measurement readout** of the fault-tolerant Toffoli gate-teleportation circuit of Nielsen &
Chuang **Exercise 10.68** (the Figure on p. 488, part (2)). This file measures the three **data**
qubits `d_x, d_y, d_z` (the right qubit of each ancilla↔data pair) *through the `Measurement`
primitive*, so that "measure the three data qubits and apply the classically-controlled
corrections" is in the primitives rather than merely annotated.

## Main declarations
* `toffoliDataMeasurement` — the **joint measurement of the three data qubits**: the two control
  data qubits `d_x, d_y` in the *computational* (`Z`) basis (`zSignMeasurement`) and the
  target data qubit `d_z` in the `X` basis (`xSignMeasurement`), each acting on the *right* qubit
  of its ancilla↔data pair (identity on the ancilla). A genuine `Measurement`, from
  the single-qubit basis measurements by `Measurement.onRight` / `Measurement.onLeft` /
  `Measurement.cascade`; the joint outcome is `(m₁, m₂, m₃) : Fin 2 × Fin 2 × Fin 2`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

set_option maxHeartbeats 1600000 in
-- Type-checking the two cascades of `onLeft`/`onRight` lifts over the 64-dimensional coupled-pairs
-- register exceeds the default elaboration budget.
/-- **The joint measurement of the three data qubits** (Nielsen & Chuang, Exercise 10.68, the three
data-qubit measurements of the Figure on p. 488). On the coupled-pairs register `(a₁ ⊗ d_x) ⊗
((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))`, measure the right (data) qubit of each pair — `d_x, d_y` in the
computational (`Z`) basis (`zSignMeasurement`), `d_z` in the `X` basis (`xSignMeasurement`) —
leaving the ancilla (left) qubits untouched. A genuine `Measurement`. -/
def toffoliDataMeasurement :
    Measurement (Fin 2 × Fin 2 × Fin 2)
      ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  ((zSignMeasurement.onRight qubit).onLeft ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).cascade
    ((((zSignMeasurement.onRight qubit).onLeft (qubit ⊗ qubit)).cascade
        ((xSignMeasurement.onRight qubit).onRight (qubit ⊗ qubit))).onRight (qubit ⊗ qubit))

end AxQM
