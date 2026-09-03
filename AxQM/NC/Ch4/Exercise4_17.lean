/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledZ
import AxQM.NC.Ch2.Exercise2_52

/-!
# Nielsen & Chuang, Exercise 4.17 (Building CNOT from controlled-`Z` gates)

*(N&C p. 179.)*

Construct CNOT from one controlled-Z gate and two Hadamard gates.

* `cnotGate_eq_hadamard_conj_controlledZGate`
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.17: `CNOT` from one controlled-`Z` gate and two Hadamards.** The
controlled-`NOT` gate equals the controlled-`Z` gate `controlledZGate` conjugated on its
**target** qubit by a Hadamard on each side: `cnotGate = (1 ⊗ H) · controlledZGate · (1 ⊗ H)`,
where `Evolution.onRight hadamardGate qubit = 1 ⊗ H` applies `H` to the target (right) qubit
while leaving the control (left) qubit untouched. -/
theorem cnotGate_eq_hadamard_conj_controlledZGate :
    cnotGate = (Evolution.onRight hadamardGate qubit).comp
      (controlledZGate.comp (Evolution.onRight hadamardGate qubit)) := sorry

end AxQM
