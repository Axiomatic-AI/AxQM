/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.MeasurementCoarseGrain
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.CascadedMeasurement
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.BellReducedState
import AxQM.Basic.API.PhaseFlipCode

/-!
# AxQM.Basic.API — local `Z`/`X` measurements vs. Bell projectors `Π_bf`/`Π_pf`

Alice and Bob each measuring `Z` (resp. `X`) locally, and the coarse-graining coordinates along
which those local measurements are compared with the Bell measurement.

## Contents

* `localZMeasurement`, `localXMeasurement` — Alice and Bob each measure `Z` (resp. `X`) locally:
  the cascade of the two single-qubit sign measurements, a four-outcome joint measurement.
* `zParity (a, b) = a + b`, `xParity (a, b) = a + b` — the compiled statistic "did the two local
  outcomes disagree?".
* `bitFlipIndex (x, y) = y`, `phaseFlipIndex (x, y) = x` — the Bell-measurement coordinates
  detecting a bit flip and a phase flip.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- The single-qubit `Z` (sign) measurement, outcome `0 ↔ +1` (`|0⟩`), `1 ↔ −1` (`|1⟩`). -/
def zSignMeasurement : Measurement (Fin 2) qubit :=
  pauliZObservable.signMeasurement pauliZObservable_op_mul_self

/-- **Alice and Bob each measure `Z` locally.**  The joint local `Z` measurement is the cascade of
the two single-qubit `Z` sign measurements — `zSignMeasurement` on the left factor (Alice), then on
the right factor (Bob) — a genuine four-outcome `Measurement (Fin 2 × Fin 2)`. -/
def localZMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ qubit) :=
  (zSignMeasurement.onLeft qubit).cascade (zSignMeasurement.onRight qubit)

/-- **The compiled bit-flip statistic** `a + b`: Alice and Bob record whether their two local `Z`
outcomes *disagree* (`a + b = 1`, a bit flip) or *agree* (`a + b = 0`). -/
def zParity : Fin 2 × Fin 2 → Fin 2 := fun p => p.1 + p.2

/-- **The bit-flip outcome coordinate** of the Bell measurement: `|β_xy⟩` carries a bit flip iff
`y = 1`. -/
def bitFlipIndex : Fin 2 × Fin 2 → Fin 2 := fun p => p.2

/-- The single-qubit `X` (sign) measurement, outcome `0 ↔ +1` (`|+⟩`), `1 ↔ −1` (`|−⟩`). -/
def xSignMeasurement : Measurement (Fin 2) qubit :=
  pauliXObservable.signMeasurement pauliXObservable_op_mul_self

/-- **Alice and Bob each measure `X` locally.**  The joint local `X` measurement is the cascade of
the two single-qubit `X` sign measurements — `xSignMeasurement` on the left factor (Alice), then
on the right factor (Bob) — a genuine four-outcome `Measurement (Fin 2 × Fin 2)`. -/
def localXMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ qubit) :=
  (xSignMeasurement.onLeft qubit).cascade (xSignMeasurement.onRight qubit)

/-- **The compiled phase-flip statistic** `a + b`: Alice and Bob record whether their two local `X`
outcomes *disagree* (`a + b = 1`, a phase flip) or *agree* (`a + b = 0`). -/
def xParity : Fin 2 × Fin 2 → Fin 2 := fun p => p.1 + p.2

/-- **The phase-flip outcome coordinate** of the Bell measurement: `|β_xy⟩` carries a phase flip iff
`x = 1`. -/
def phaseFlipIndex : Fin 2 × Fin 2 → Fin 2 := fun p => p.1

end AxQM
