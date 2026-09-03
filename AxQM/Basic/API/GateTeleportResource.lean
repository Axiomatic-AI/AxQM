/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellBasis
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.Associator

/-!
# AxQM.Basic.API — the gate-teleportation resource state

The **four-qubit entangled resource state** of Nielsen & Chuang **Problem 4.6** ("Universality
with prior entanglement"): the Gottesman–Chuang state obtained by applying a `CNOT` to one half
of each of two Bell pairs.  This is resource #3 of Problem 4.6 — one instance of the ability to
prepare an arbitrary four-qubit entangled state.

## Main declarations
* `gateTeleportReshape` — the regrouping `(q⊗q)⊗(q⊗q) ≃ₛ q ⊗ ((q⊗q)⊗q)` bringing the two middle
  qubits `(a_out, b_out)` together.
* `cnotMiddleGate` — the placed `CNOT` `1 ⊗ (CNOT ⊗ 1)` on the regrouped register.
* `cnotGateTeleportResource` — the **resource state** `|χ⟩`: `CNOT` applied to the two output
  halves of `bellPhiPlus ⊗ bellPhiPlus`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- The structural regrouping `(q⊗q)⊗(q⊗q) ≃ₛ q ⊗ ((q⊗q)⊗q)` of the four-qubit register `a_in a_out
b_out b_in`: re-associate so the two middle qubits `(a_out, b_out)` form a tensor factor. -/
def gateTeleportReshape :
    ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ≃ₛ (qubit ⊗ ((qubit ⊗ qubit) ⊗ qubit)) :=
  (QSystem.assoc qubit qubit (qubit ⊗ qubit)).symm.trans
    (QSystem.Iso.tmul (QSystem.Iso.refl qubit) (QSystem.assoc qubit qubit qubit))

/-- `CNOT` on the middle two qubits `(a_out, b_out)` of the regrouped register
`a_in ⊗ ((a_out b_out) ⊗ b_in)`: `1 ⊗ (CNOT ⊗ 1)`, i.e. identity on `a_in` and `b_in`, `cnotGate`
on `(a_out, b_out)`. -/
def cnotMiddleGate : Evolution (qubit ⊗ ((qubit ⊗ qubit) ⊗ qubit)) :=
  Evolution.onRight (Evolution.onLeft cnotGate qubit) qubit

/-- The **four-qubit gate-teleportation resource state** `|χ⟩` of Nielsen & Chuang Problem 4.6
(resource #3): `CNOT` applied to the two output halves of two Bell pairs. -/
def cnotGateTeleportResource : PureState ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) :=
  PureState.congr gateTeleportReshape.symm
    (cnotMiddleGate.evolvePure (PureState.congr gateTeleportReshape (bellPhiPlus.tmul bellPhiPlus)))

end AxQM
