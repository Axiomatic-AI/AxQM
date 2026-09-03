/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fredkin

/-!
# AxQM.Basic.API — the Toffoli gate-teleportation coupling

The **data↔ancilla coupling** of the fault-tolerant Toffoli circuit of Nielsen & Chuang Exercise
10.68 (the Figure on p. 488, part (2)), and the **pre-measurement gate-teleportation state** it
produces — the Toffoli analogue of the π/8-gate circuit output `Concrete.piEighthCircuitOut` (whose
measured branches `Concrete.piEighthCircuitOut_measure_zero / _measure_one` are the reduction
core of Exercise 10.66).

## Main declarations
* `toffoliTeleportCoupling` — the coupling `Evolution` `CNOT(a₁→d_x) · CNOT(a₂→d_y) · CNOT(d_z→a₃)`.
  The two control couplings are `cnotGate` (ancilla = control); the target coupling is
  `reversedCnotGate` (data = control), matching the Figure's reversed arrow on the target wire.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 800000 in
-- The coupling `Evolution` lives on the 64-dimensional coupled-pairs register; composing the three
-- blockwise gates there exceeds the default elaboration budget.
/-- **The Toffoli gate-teleportation coupling** (Nielsen & Chuang, Exercise 10.68 part (2), the
three `CNOT`s of the Figure on p. 488): on the coupled-pairs register `(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y)
⊗ (a₃ ⊗ d_z))` — the three ancilla↔data pairs laid adjacently — apply

`CNOT(a₁ → d_x)` on the first pair, `CNOT(a₂ → d_y)` on the second, and `CNOT(d_z → a₃)` on the
third.

The two control pairs use `cnotGate` (ancilla = control, data = target); the target pair uses
`reversedCnotGate` (data `d_z` = control, ancilla `a₃` = target), matching the reversed arrow on
the target wire of the Figure.
-/
def toffoliTeleportCoupling :
    Evolution ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  (cnotGate.onLeft ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).comp
    (((cnotGate.onLeft (qubit ⊗ qubit)).onRight (qubit ⊗ qubit)).comp
      ((reversedCnotGate.onRight (qubit ⊗ qubit)).onRight (qubit ⊗ qubit)))

end AxQM
