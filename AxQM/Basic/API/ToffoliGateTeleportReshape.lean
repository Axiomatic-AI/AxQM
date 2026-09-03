/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ToffoliGateTeleport
import AxQM.Basic.API.ToffoliAncilla
import AxQM.Basic.API.Interchange

/-!
# AxQM.Basic.API — the Toffoli gate-teleportation reshape

The **register reshape** connecting the physical layout of the fault-tolerant Toffoli circuit of
Nielsen & Chuang Exercise 10.68 (the ancilla block prepared offline beside the data block) to the
*coupled-pairs* register on which the data↔ancilla coupling `toffoliTeleportCoupling` acts. It is
the Toffoli analogue of the CNOT gate-teleportation reshape `gateTeleportProtocolReshape`.

## Main declarations
* `toffoliTeleportReshape` — the reshape system isomorphism `(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗
  (qubit ⊗ qubit)) ≃ₛ (qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))` interleaving the
  ancilla and data three-qubit blocks into the three coupled pairs.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 1000000 in
-- The type-check of this nested composite of transport-backbone isos over the 64-dimensional
-- register exceeds the default heartbeat budget; the elaboration is pure `QSystem.Iso` data.
/-- **The Toffoli gate-teleportation reshape** (Nielsen & Chuang, Exercise 10.68 part (2)): the
system isomorphism `(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit)) ≃ₛ (qubit ⊗ qubit) ⊗
((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))` that interleaves the offline **ancilla block** `a₁ ⊗ (a₂ ⊗
a₃)` and the **data block** `x ⊗ (y ⊗ z)` — laid side by side in the physical register — into
the three coupled ancilla–data pairs `(a₁ ⊗ x)`, `(a₂ ⊗ y)`, `(a₃ ⊗ z)` on which the coupling
`toffoliTeleportCoupling` acts. -/
def toffoliTeleportReshape :
    ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit)))
      ≃ₛ ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  (QSystem.Iso.interchange qubit (qubit ⊗ qubit) qubit (qubit ⊗ qubit)).trans
    (QSystem.Iso.tmul (QSystem.Iso.refl (qubit ⊗ qubit))
      (QSystem.Iso.interchange qubit qubit qubit qubit))

end AxQM
