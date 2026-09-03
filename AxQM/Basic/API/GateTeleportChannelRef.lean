/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GateTeleportMeasurement
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.Associator

/-!
# AxQM.Basic.API — the gate-teleportation `CNOT` channel with an external reference

The gate-teleportation gadget of Nielsen & Chuang **Problem 4.6** (`GateTeleport{Measurement,
Correction,Channel}.lean`) implements `CNOT` on a *standalone* two-qubit input `ψ`.  For the
**universality** conclusion — that the resource set is universal on **every** register — one must
run the gadget on two *wires* of a larger `n`-qubit register, wires that are generally **entangled
with the other wires**.  That is the induced-operation-tensors-with-identity step: the gadget acts
on its two input wires and identity on everything else, correctly *even when the input is entangled
with a reference system* `R`.

## Main declarations
* `gateTeleportRegisterGenRef R Ψ` — the protocol register for an input pure state `Ψ` of the
  composite `R ⊗ (qubit ⊗ qubit)` (the two `CNOT` input wires together with an arbitrary reference
  `R`): the input beside the four-qubit resource `|χ⟩`, reshaped so that `R` rides on the left and
  the six-qubit gate-teleportation register sits on the right, ready for the two Bell measurements.
  The point is that `Ψ` may be **entangled** across `R` and the two input wires.
-/

open scoped TensorProduct

namespace AxQM

set_option maxHeartbeats 1000000 in
-- Elaboration of the reference-augmented reshape over the seven-way composite space (`R` beside
-- the six-qubit register) is defeq-heavy; the default heartbeat budget is insufficient.
/-- **The gate-teleportation protocol register with an external reference** `R`. For an input pure
state `Ψ` of `R ⊗ (qubit ⊗ qubit)` — the two `CNOT` input wires together with an arbitrary
reference `R` they may be entangled with — this is the input beside the four-qubit resource
`|χ⟩` (`cnotGateTeleportResource`), transported so that `R` rides on the left and the six-qubit
gate-teleportation register (two measured pairs on the left, the two output halves on the right)
sits on the right. -/
noncomputable def gateTeleportRegisterGenRef (R : QSystem)
    (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) :
    PureState (R.compose (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit))) :=
  PureState.congr
    ((R.assoc (qubit ⊗ qubit) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).symm.trans
      ((QSystem.Iso.refl R).tmul gateTeleportProtocolReshape))
    (Ψ.tmul cnotGateTeleportResource)

end AxQM
