/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledZ

/-!
# Nielsen & Chuang, Exercise 7.32 (the ion-trap `CNOT` circuit of Figure 7.14)

*(N&C p. 324.)*

Show the ion-trap circuit of Fig 7.14 is equivalent (up to phases) to a controlled-NOT with phonon
as control.

* `ionTrapCnotCircuit` — the circuit of Figure 7.14 as an `Evolution` on `qubit ⊗ qubit`,
  `R_y(-π/2)₂ · CZ · R_y(π/2)₂`, with the two rotations placed on the right (internal-state) qubit
  via `Evolution.onRight` and `CZ = controlledZGate`.
* `ionTrapCnotCircuit_eq_pauliZ_control_comp_cnot` — Exercise 7.32: `ionTrapCnotCircuit = (Z ⊗ 1) ·
  CNOT`, an exact equality of two-qubit gates in which `CNOT` has the phonon (first) qubit as
  control and the prefactor `Z ⊗ 1 = diag(1, 1, -1, -1)` is a *relative phase* (a diagonal,
  unit-modulus, basis-state-dependent phase, not a global one).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The ion-trap controlled-`NOT` circuit of Nielsen & Chuang, Figure 7.14** as an `Evolution` on
`qubit ⊗ qubit` (phonon ⊗ internal-state). Following N&C's three-pulse realisation (p. 322),
reading right to left: an `R_y(π/2)` rotation on the internal-state (second) qubit, then a
controlled-`Z` between the two qubits, then an `R_y(-π/2)` rotation on the internal-state qubit
— `R_y(-π/2)₂ · CZ · R_y(π/2)₂`. -/
def ionTrapCnotCircuit : Evolution (qubit ⊗ qubit) :=
  ((rotYGate (-(Real.pi / 2))).onRight qubit).comp
    (controlledZGate.comp ((rotYGate (Real.pi / 2)).onRight qubit))

/-- **Nielsen & Chuang, Exercise 7.32.** The Figure 7.14 circuit is a controlled-`NOT` with the
**phonon** (first qubit) as control, up to relative phases: `ionTrapCnotCircuit = (Z ⊗ 1) ·
CNOT`, an exact equality of two-qubit gates. Here `CNOT = cnotGate` has the phonon (first) qubit
as control and the internal-state (second) qubit as target, and the prefactor `Z ⊗ 1 =
pauliZGate.onLeft qubit = diag(1, 1, -1, -1)` is a *relative* phase — diagonal, of unit modulus,
depending on the (phonon) basis state, not a single global scalar. On a computational-basis
input this reads `(Z ⊗ 1)·CNOT |q₁, q₂⟩ = (-1)^{q₁} |q₁, q₂ ⊕ q₁⟩`: the `CNOT` truth table
(phonon `q₁` controls the flip of the ion qubit `q₂`) up to the relative phase `(-1)^{q₁}`.
-/
theorem ionTrapCnotCircuit_eq_pauliZ_control_comp_cnot :
    ionTrapCnotCircuit = (pauliZGate.onLeft qubit).comp cnotGate := sorry

end AxQM
