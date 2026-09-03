/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ToffoliPauliPropagation

/-!
# Nielsen & Chuang, Exercise 10.67 (Toffoli error-propagation circuit identities)

*(N&C p. 487.)*

Show the given circuit identities (a) and (b) hold (X/Z propagation through controlled gates).

* `toffoliGate_comp_pauliXGate_control_propagates` — identity (a): an `X` on the first control
  copies onto the target *conditioned on the second control*, `T·X₁ = (X₁·CNOT₂₃)·T`.
* `toffoliGate_comp_pauliZGate_target_propagates` — identity (b): a `Z` on the target copies *back*
  onto the two controls as a controlled-`Z`, `T·Z₃ = (Z₃·CZ₁₂)·T`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Identity (a) of N&C Exercise 10.67:** an `X` on the first control of the Toffoli propagates,
past the gate, to an `X` on that control together with a `CNOT` from the second control to the
target: `T · X₁ = (X₁ · CNOT₂₃) · T` on `qubit ⊗ (qubit ⊗ qubit)`, where `X₁ = pauliXGate.onLeft
(qubit ⊗ qubit)` and `CNOT₂₃ = cnotGate.onRight qubit`. -/
theorem toffoliGate_comp_pauliXGate_control_propagates :
    toffoliGate.comp (pauliXGate.onLeft (qubit ⊗ qubit))
      = ((pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit)).comp toffoliGate :=
        sorry

/-- **Identity (b) of N&C Exercise 10.67:** a `Z` on the Toffoli target propagates, past the gate,
*back* to a `Z` on the target together with a controlled-`Z` between the two controls:
`T · Z₃ = (Z₃ · CZ₁₂) · T` on `qubit ⊗ (qubit ⊗ qubit)`, where `Z₃ = (pauliZGate.onRight
qubit).onRight qubit` and `CZ₁₂ = controlledZLeftGate`. -/
theorem toffoliGate_comp_pauliZGate_target_propagates :
    toffoliGate.comp ((pauliZGate.onRight qubit).onRight qubit)
      = (((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate).comp toffoliGate :=
        sorry

end AxQM
