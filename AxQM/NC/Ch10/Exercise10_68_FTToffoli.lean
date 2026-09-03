/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.QubitThree
import AxQM.Basic.API.Swap
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.ControlBranchExt
import AxQM.Basic.API.ToffoliGateTeleportCompose
import AxQM.NC.Ch10.Exercise10_67

/-!
# Nielsen & Chuang, Exercise 10.68 (Fault-tolerant Toffoli gate construction)

*(N&C p. 488.)*

Fault-tolerant Toffoli gate construction via swap+Toffoli circuit and commutation moves (Steane
code).

* `swapThenToffoli` — Part (1): the circuit that swaps the three-qubit data block `|ψ⟩` with a
  known `|000⟩` block and then applies a Toffoli to the block now holding the data.
* `swapThenToffoli_evolvePure_ancillaZero` — Part (1): that circuit computes the Toffoli of the
  data, `|ψ⟩ ⊗ |000⟩ ↦ |000⟩ ⊗ Toffoli|ψ⟩`.
* `toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasureGen` — Part (2): the
  measured gate-teleportation circuit implements the Toffoli gate on every input and every
  measurement outcome.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 800000 in
-- `Evolution` on the 64-dimensional composite `T₃ ⊗ T₃`: composing the two blockwise gates
-- (`toffoliGate.onRight` and `Evolution.swap`) there exceeds the default elaboration budget.
/-- **The swap-then-Toffoli circuit** (Nielsen & Chuang, Exercise 10.68 part (1)). -/
def swapThenToffoli :
    Evolution ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  (toffoliGate.onRight (qubit ⊗ (qubit ⊗ qubit))).comp Evolution.swap

/-- **Part (1): the swap-then-Toffoli circuit computes the Toffoli.** Swapping an arbitrary
three-qubit data state `|ψ⟩` with the known `|000⟩` block and then applying a Toffoli to the
block now holding the data yields `|000⟩ ⊗ Toffoli|ψ⟩`:

`swapThenToffoli (|ψ⟩ ⊗ |000⟩) = |000⟩ ⊗ Toffoli|ψ⟩`.
-/
theorem swapThenToffoli_evolvePure_ancillaZero (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) :
    swapThenToffoli.evolvePure (ψ.tmul (qubitThreeBasis (0, 0, 0)))
      = (qubitThreeBasis (0, 0, 0)).tmul (toffoliGate.evolvePure ψ) := sorry

/-! ## The assembled measured gate-teleportation identity (part (2)) -/

/-- **The assembled measured Toffoli gate-teleportation identity, for an arbitrary input** (Nielsen
& Chuang, Exercise 10.68 part (2)): the fault-tolerant Toffoli circuit implements the Toffoli
**gate**, deterministically, on **every** input state and **every** measurement outcome.

The ancilla marginal is `(toffoliGate.evolvePure ψ).toState` — the Toffoli of the *whole* input
`ψ` — **independent of the outcome** (the right-hand side does not mention `m₁, m₂, m₃`).

The input `ψ` is arbitrary, not merely one of the eight computational-basis inputs `|xyz⟩`.
-/
theorem toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasureGen
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) (m₁ m₂ m₃ : Fin 2)
    (hp : toffoliDataMeasurement.bornProb
        (toffoliTeleportPreMeasureGen ψ).toState (m₁, m₂, m₃) ≠ 0) :
    (((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).evolve
        ((toffoliDataMeasurement.postMeasurement
              (toffoliTeleportPreMeasureGen ψ).toState (m₁, m₂, m₃) hp).congr
            toffoliTeleportReshape.symm)).reducedLeft
      = (toffoliGate.evolvePure ψ).toState := sorry

end AxQM
