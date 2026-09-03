/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorLogicalOperators
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.NC.Ch10.Exercise10_6

/-!
# Nielsen & Chuang, Exercise 10.48 — the Shor-code logical operators `Z̄`, `X̄`

*(N&C p. 468.)*

Show Zbar=X1..X9 and Xbar=Z1..Z9 act as logical Z,X on the Shor code.

* `shorLogicalZBar_hasEigenstate_shorCodeword`
* `shorLogicalXBar_evolvePure_shorCodeword`
-/

open scoped TensorProduct

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.48 (`Z̄` acts as logical `Z`).** The operator `Z̄ = X₁…X₉` is
diagonal on the Shor codewords with eigenvalue `(−1)^s`: `Z̄|0_L⟩ = |0_L⟩` and `Z̄|1_L⟩ =
−|1_L⟩`, exactly as logical `Z` acts on `|0_L⟩, |1_L⟩`. -/
theorem shorLogicalZBar_hasEigenstate_shorCodeword (s : Fin 2) :
    shorLogicalZBar.HasEigenstate ((-1 : ℝ) ^ (s : ℕ)) (shorCodeword s) := sorry

/-- **Nielsen & Chuang, Exercise 10.48 (`X̄` acts as logical `X`).** The operator
`X̄ = Z₁…Z₉` swaps the Shor codewords: `X̄|s_L⟩ = |(s+1)_L⟩`, i.e. `X̄|0_L⟩ = |1_L⟩` and
`X̄|1_L⟩ = |0_L⟩`, exactly as logical `X` acts on `|0_L⟩, |1_L⟩`. -/
theorem shorLogicalXBar_evolvePure_shorCodeword (s : Fin 2) :
    shorLogicalXBar.evolvePure (shorCodeword s) = shorCodeword (s + 1) := sorry

end AxQM
