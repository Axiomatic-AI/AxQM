/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_52
import AxQM.Concrete.SteaneStandardForm

/-!
# Nielsen & Chuang, Exercise 10.55 — the `X̄` operator for the standard form of the Steane code

*(N&C p. 471.)*

Find the Xbar operator for the standard form of the Steane code.

* `steaneStandardLogicalXBar`
* `steaneStandardLogicalXBar_evolvePure_logicalZero` — `X̄|0_L⟩ = |1_L⟩`;
* `steaneStandardLogicalXBar_evolvePure_logicalOne` — `X̄|1_L⟩ = |0_L⟩`.
-/

namespace AxQM

open AxQM.Concrete

open scoped Matrix

/-- **The `X̄` operator for the standard form of the Steane code** (Nielsen & Chuang, Ex 10.55), in
the original qubit ordering: `X̄ = X₃X₅X₆`, the bit-flip Pauli string on the seven-qubit
register, as a unitary `Evolution`. -/
noncomputable def steaneStandardLogicalXBar : Evolution (bitReg (Fin 7)) :=
  bitString steaneStdLogicalXOriginalSupport

/-- **Nielsen & Chuang, Exercise 10.55 (`X̄` maps `|0_L⟩` to `|1_L⟩`).** The standard-form
logical-`X` operator `X̄ = X₃X₅X₆` sends the Steane logical zero to the logical one,
`X̄|0_L⟩ = |1_L⟩`. -/
theorem steaneStandardLogicalXBar_evolvePure_logicalZero :
    steaneStandardLogicalXBar.evolvePure steaneLogicalZero = steaneLogicalOne := sorry

/-- **Nielsen & Chuang, Exercise 10.55 (`X̄` maps `|1_L⟩` to `|0_L⟩`).** The standard-form
logical-`X` operator `X̄ = X₃X₅X₆` sends the Steane logical one back to the logical zero,
`X̄|1_L⟩ = |0_L⟩`. -/
theorem steaneStandardLogicalXBar_evolvePure_logicalOne :
    steaneStandardLogicalXBar.evolvePure steaneLogicalOne = steaneLogicalZero := sorry

end AxQM
