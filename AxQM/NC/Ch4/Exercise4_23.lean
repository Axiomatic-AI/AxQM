/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledRotation
import AxQM.NC.Ch2.Exercise2_52

/-!
# Nielsen & Chuang, Exercise 4.23 — constructing `C¹(U)` for `U = R_x(θ)`, `R_y(θ)`

*(N&C p. 181.)*

Construct C^1(U) for U=R_x/R_y using CNOT and single-qubit gates; minimize.

* `controlledUnitary_rotYGate` — the reduced controlled-`R_y` construction: `C(R_y(θ)) = (1 ⊗
  R_y(θ/2)) · CNOT · (1 ⊗ R_y(-θ/2)) · CNOT`, using two single-qubit gates and two `CNOT`s — the `3
  → 2` reduction the exercise asks for.
* `controlledUnitary_rotXGate` — the controlled-`R_x` construction: `C(R_x(θ)) = (1 ⊗ H) · (1 ⊗
  R_z(θ/2)) · CNOT · (1 ⊗ R_z(-θ/2)) · CNOT · (1 ⊗ H)`, built from `CNOT` and three single-qubit
  gates.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.23 (controlled-`R_y`, reduced to two single-qubit gates).** The
controlled-`R_y(θ)` gate is realised from two `CNOT`s and just two single-qubit gates:
`C(R_y(θ)) = (1 ⊗ R_y(θ/2)) · CNOT · (1 ⊗ R_y(-θ/2)) · CNOT`, where `Evolution.onRight (rotYGate
_) qubit = 1 ⊗ R_y(_)` applies the rotation to the target (right) qubit while leaving the
control untouched.
-/
theorem controlledUnitary_rotYGate (θ : ℝ) :
    controlledUnitary (rotYGate θ)
      = (((rotYGate (θ / 2)).onRight qubit).comp cnotGate).comp
          (((rotYGate (-(θ / 2))).onRight qubit).comp cnotGate) := sorry

/-- **Nielsen & Chuang, Exercise 4.23 (controlled-`R_x`).** The controlled-`R_x(θ)` gate is realised
from `CNOT` and three single-qubit gates.
-/
theorem controlledUnitary_rotXGate (θ : ℝ) :
    controlledUnitary (rotXGate θ)
      = (hadamardGate.onRight qubit).comp
          (((((rotZGate (θ / 2)).onRight qubit).comp cnotGate).comp
              (((rotZGate (-(θ / 2))).onRight qubit).comp cnotGate)).comp
            (hadamardGate.onRight qubit)) := sorry

end AxQM
