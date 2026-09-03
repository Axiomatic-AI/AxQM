/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary

/-!
# Nielsen & Chuang, Exercise 4.21 (Figure 4.8 implements the `C²(U)` operation)

*(N&C p. 181.)*

Verify Figure 4.8 implements the C^2(U) operation.

* `ccontrolledUnitaryCircuit`
* `ccontrolledUnitaryCircuit_eq_ccontrolledUnitary`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Figure 4.8 circuit** (Nielsen & Chuang §4.3) implementing `C²(V²)` from a single-qubit
square-root gate `V`, on the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)`
(control₁ ⊗ (control₂ ⊗ target)). Reading the circuit left to right — the leftmost gate acts
first, so it is the *innermost* `Evolution.comp` — the five gates are: `C(V)` on `(c₂, t)`,
`CNOT` on `(c₁, c₂)`, `C(V†)` on `(c₂, t)`, `CNOT` on `(c₁, c₂)`, `C(V)` on `(c₁, t)`. -/
def ccontrolledUnitaryCircuit (V : Evolution qubit) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (controlledUnitary (V.onRight qubit)).comp
    ((controlledUnitary (pauliXGate.onLeft qubit)).comp
      (((controlledUnitary V.adjoint).onRight qubit).comp
        ((controlledUnitary (pauliXGate.onLeft qubit)).comp
          ((controlledUnitary V).onRight qubit))))

/-- **Nielsen & Chuang, Exercise 4.21.** The Figure 4.8 circuit implements `C²(U)` for `U = V²`,
where `V` is an arbitrary single-qubit gate and `V†` is the adjoint gate `V.adjoint = V⁻¹`.
-/
theorem ccontrolledUnitaryCircuit_eq_ccontrolledUnitary (V : Evolution qubit) :
    ccontrolledUnitaryCircuit V = ccontrolledUnitary (V.comp V) := sorry

end AxQM
