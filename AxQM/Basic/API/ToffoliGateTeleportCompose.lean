/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ToffoliGateTeleportCorrection
import AxQM.Basic.API.ToffoliGateTeleportReshape
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.Swap
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.Composite
import AxQM.Basic.API.QubitThree
import AxQM.Basic.API.PhaseFlipStabilizerMaximality
import AxQM.Basic.PartialTrace

/-!
# AxQM.Basic.API — assembling the Toffoli gate-teleportation identity

The **underlying operator bridges** for the assembled corrected gate-teleportation identity of
Nielsen & Chuang
**Exercise 10.68** (the Figure on p. 488, part (2)) — the final step composing the classically
controlled byproduct corrections with the *actual*
measured state on the coupled-pairs register.

## Main declarations
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

set_option maxHeartbeats 800000 in
-- `evolvePure` of the coupling on the 64-dimensional coupled-pairs register exceeds the default.
/-- **The pre-measurement gate-teleportation state for a general input** `ψ`. Taking `ψ` an
*arbitrary* three-qubit pure state — possibly entangled with the two control wires — is what
makes the identity below "the circuit implements the Toffoli **gate**", not just its truth
table. -/
def toffoliTeleportPreMeasureGen (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) :
    PureState ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  toffoliTeleportCoupling.evolvePure
    (PureState.congr toffoliTeleportReshape (toffoliAncilla.tmul ψ))

end AxQM
