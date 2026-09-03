/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EPRLocalMeasurement
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.37 — measuring one EPR qubit collapses the other

*(N&C p. 598.)*

Show measuring one EPR qubit in X (resp Z) collapses other into X (Z) eigenstate.

* `eprMeasureFirstZ_postMeasurement_zero` — `Z` basis: outcome `+1` → `|0⟩ ⊗ |0⟩`;
* `eprMeasureFirstZ_postMeasurement_one` — `Z` basis: outcome `−1` → `|1⟩ ⊗ |1⟩`;
* `eprMeasureFirstX_postMeasurement_zero` — `X` basis: outcome `+1` → `|+⟩ ⊗ |+⟩`;
* `eprMeasureFirstX_postMeasurement_one` — `X` basis: outcome `−1` → `|-⟩ ⊗ |-⟩`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### `Z`-basis measurement of the first qubit -/

/-- **Nielsen & Chuang, Exercise 12.37 (`Z` basis, outcome `+1`).** Measuring the first qubit of the
EPR pair `|Φ⁺⟩` in the `Z` basis and obtaining `+1` (outcome `0`) collapses the joint state to the
product `|0⟩ ⊗ |0⟩`: the second qubit is left in the `Z` eigenstate `|0⟩`. -/
theorem eprMeasureFirstZ_postMeasurement_zero
    (hp : eprMeasureFirstZ.bornProb bellPhiPlus.toState 0 ≠ 0) :
    eprMeasureFirstZ.postMeasurement bellPhiPlus.toState 0 hp
      = (qubitBasis 0 ⊗ qubitBasis 0).toState := sorry

/-- **Nielsen & Chuang, Exercise 12.37 (`Z` basis, outcome `−1`).** Measuring the first qubit of
`|Φ⁺⟩` in the `Z` basis and obtaining `−1` (outcome `1`) collapses the joint state to `|1⟩ ⊗ |1⟩`:
the second qubit is left in the `Z` eigenstate `|1⟩`. -/
theorem eprMeasureFirstZ_postMeasurement_one
    (hp : eprMeasureFirstZ.bornProb bellPhiPlus.toState 1 ≠ 0) :
    eprMeasureFirstZ.postMeasurement bellPhiPlus.toState 1 hp
      = (qubitBasis 1 ⊗ qubitBasis 1).toState := sorry

/-! ### `X`-basis measurement of the first qubit -/

/-- **Nielsen & Chuang, Exercise 12.37 (`X` basis, outcome `+1`).** Measuring the first qubit of the
EPR pair `|Φ⁺⟩` in the `X` basis and obtaining `+1` (outcome `0`) collapses the joint state to the
product `|+⟩ ⊗ |+⟩`: the second qubit is left in the `X` eigenstate `|+⟩`. -/
theorem eprMeasureFirstX_postMeasurement_zero
    (hp : eprMeasureFirstX.bornProb bellPhiPlus.toState 0 ≠ 0) :
    eprMeasureFirstX.postMeasurement bellPhiPlus.toState 0 hp
      = (qubitPlus ⊗ qubitPlus).toState := sorry

/-- **Nielsen & Chuang, Exercise 12.37 (`X` basis, outcome `−1`).** Measuring the first qubit of
`|Φ⁺⟩` in the `X` basis and obtaining `−1` (outcome `1`) collapses the joint state to `|-⟩ ⊗ |-⟩`:
the second qubit is left in the `X` eigenstate `|-⟩`. -/
theorem eprMeasureFirstX_postMeasurement_one
    (hp : eprMeasureFirstX.bornProb bellPhiPlus.toState 1 ≠ 0) :
    eprMeasureFirstX.postMeasurement bellPhiPlus.toState 1 hp
      = (qubitMinus ⊗ qubitMinus).toState := sorry

end AxQM
