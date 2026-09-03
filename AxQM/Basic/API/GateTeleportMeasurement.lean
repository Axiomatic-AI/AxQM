/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GateTeleportProtocolReshape
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.PhaseEstimationSuperposition
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# AxQM.Basic.API — the Bell-measurement readout of gate teleportation

The Bell measurement of the Gottesman–Chuang gate-teleportation protocol for `CNOT`
(Nielsen & Chuang **Problem 4.6**).

## Main declarations
* `bellPairsMeasurement` — the **joint Bell measurement of the two co-located measured pairs**: the
  Bell-basis measurement of the left block (each pair measured in the Bell basis), tensored with the
  identity on the output pair.
-/

namespace AxQM

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

/-- **The joint Bell measurement of the two co-located pairs** (Problem 4.6 resource #2, applied to
both measured pairs of the protocol register).  Each of the two pairs of the left block is measured
in the Bell basis, with the identity on the output pair; the joint outcome is the pair of Bell
outcomes `(p, q)`.  A genuine `Measurement`. -/
noncomputable def bellPairsMeasurement :
    Measurement ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))
      (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)) :=
  (bellMeasurement.leftAndBasisRight bellBasis).onLeft (qubit ⊗ qubit)

end AxQM
