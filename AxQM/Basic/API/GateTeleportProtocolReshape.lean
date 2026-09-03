/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.GateTeleportResource
import AxQM.Basic.API.Interchange
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.ControlledUnitaryDecomposition

/-!
# AxQM.Basic.API — the gate-teleportation protocol reshape

The **protocol register reshape** of Nielsen & Chuang **Problem 4.6** ("Universality with prior
entanglement") — the six-qubit regrouping that lays out the gate-teleportation register for the
two Bell measurements and the co-located `CNOT` output.

## Main declarations
* `gateTeleportProtocolReshape` — the reshape system isomorphism `(q ⊗ q) ⊗ ((q ⊗ q) ⊗ (q ⊗ q)) ≃ₛ
  ((q ⊗ q) ⊗ (q ⊗ q)) ⊗ (q ⊗ q)` sending `(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_out ⊗ b_in))` to `((q_A
  ⊗ a_in) ⊗ (q_B ⊗ b_in)) ⊗ (a_out ⊗ b_out)`: measured pairs blocked on the left, teleported outputs
  co-located on the right.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

set_option maxHeartbeats 1000000 in
-- The type-check of this deeply nested composite of transport-backbone isos (two `interchange`
-- braids over composite systems, plus an inner `tmul`/`comm`/`assoc`) exceeds the default
-- heartbeat budget; the elaboration itself is pure `QSystem.Iso` data (no proof search).
/-- The **gate-teleportation protocol reshape** `(q ⊗ q) ⊗ ((q ⊗ q) ⊗ (q ⊗ q)) ≃ₛ ((q ⊗ q) ⊗ (q ⊗
q)) ⊗ (q ⊗ q)`. On the physical register `(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_out ⊗ b_in))` it
produces `((q_A ⊗ a_in) ⊗ (q_B ⊗ b_in)) ⊗ (a_out ⊗ b_out)`. -/
def gateTeleportProtocolReshape :
    ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)))
      ≃ₛ (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)) :=
  (QSystem.Iso.interchange qubit qubit (qubit ⊗ qubit) (qubit ⊗ qubit)).trans
    ((QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
        ((QSystem.Iso.tmul (QSystem.Iso.refl qubit) (QSystem.Iso.comm qubit qubit)).trans
          (QSystem.assoc qubit qubit qubit))).trans
      (QSystem.Iso.interchange (qubit ⊗ qubit) qubit (qubit ⊗ qubit) qubit))

end AxQM
