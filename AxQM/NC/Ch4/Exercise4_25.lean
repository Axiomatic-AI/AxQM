/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.TwoQubitGateCircuit
import AxQM.Basic.API.Fredkin
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.ControlBranchExt
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.AxisAngleGateValues
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.PhaseFlipCode
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ

/-!
# Nielsen & Chuang, Exercise 4.25 (Fredkin gate construction)

*(N&C p. 182.)*

Construct the Fredkin (controlled-swap) gate from Toffoli/CNOT; minimize gates.

* `fredkinGate_eq_toffoli_comp_middleToffoli_comp_toffoli` — Part 1: the Fredkin gate is the product
  of three Toffoli gates, `Fredkin = Toffoli · middleToffoli · Toffoli`.
* `fredkinGate_eq_cnot_comp_middleToffoli_comp_cnot` — Part 2: the first and last Toffoli gates may
  be replaced by (uncontrolled) `CNOT` gates on the target pair, `Fredkin = (I ⊗ CNOT) ·
  middleToffoli · (I ⊗ CNOT)`.
* `exists_twoQubitCircuit_eq_fredkinGate_six` — Part 3: a Fredkin construction using only six
  two-qubit gates, `∃ gs, twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 6`.
* `exists_twoQubitCircuit_eq_fredkinGate_five` — Part 4: the even simpler Smolin–DiVincenzo
  construction using only five two-qubit gates, `∃ gs, twoQubitCircuit gs = fredkinGate ∧
  twoQubitCount gs = 5`.
-/

noncomputable section

namespace AxQM

/-! ### Parts 1 & 2: the three-Toffoli and Toffoli + two-`CNOT` constructions -/

/-- **Nielsen & Chuang Exercise 4.25, Part 1 (three-Toffoli construction).** The Fredkin
(controlled-swap) gate is the product of three Toffoli gates, `Fredkin = Toffoli · middleToffoli
· Toffoli`. The two outer gates are the ordinary Toffoli `toffoliGate` (controls 1, 2; target 3)
and the middle gate is `middleToffoliGate` (controls 1, 3; target 2). -/
theorem fredkinGate_eq_toffoli_comp_middleToffoli_comp_toffoli :
    fredkinGate = toffoliGate.comp (middleToffoliGate.comp toffoliGate) := sorry

/-- **Nielsen & Chuang Exercise 4.25, Part 2 (first and last Toffoli replaced by `CNOT`).** In the
three-Toffoli construction the two outer Toffoli gates may be replaced by (uncontrolled) `CNOT`
gates on the target pair, `Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)`. -/
theorem fredkinGate_eq_cnot_comp_middleToffoli_comp_cnot :
    fredkinGate
      = (cnotGate.onRight qubit).comp (middleToffoliGate.comp (cnotGate.onRight qubit)) := sorry

/-! ### Part 3: the six-two-qubit-gate construction -/

/-- **The Fredkin gate is implementable by six two-qubit gates** (Exercise 4.25 part 3, existence
form). There is a `TwoQubitGate3` circuit whose evolution is `fredkinGate` and whose
`twoQubitCount` is `6`. -/
theorem exists_twoQubitCircuit_eq_fredkinGate_six :
    ∃ gs : List TwoQubitGate3,
      twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 6 := sorry

/-! ### Part 4: the five-two-qubit-gate construction (Smolin–DiVincenzo) -/

/-- **The Fredkin gate is implementable by five two-qubit gates** (Exercise 4.25 part 4, existence
form). There is a `TwoQubitGate3` circuit whose evolution is `fredkinGate` and whose
`twoQubitCount` is `5` — the strongest of the four constructions in the exercise. -/
theorem exists_twoQubitCircuit_eq_fredkinGate_five :
    ∃ gs : List TwoQubitGate3,
      twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 5 := sorry

end AxQM
