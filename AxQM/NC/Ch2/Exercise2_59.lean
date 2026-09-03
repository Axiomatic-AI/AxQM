/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Variance

/-!
# Nielsen & Chuang, Exercise 2.59

*(N&C p. 90.)*

For qubit |0> measure observable X: find average value and standard deviation.

* `expectation_pauliX_qubitBasis_zero` — the average value `⟪X⟫ = 0`.
* `stdDev_pauliX_qubitBasis_zero` — the standard deviation `Δ(X) = 1`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Average value of `X` in `|0⟩` is `0`** (Nielsen & Chuang, Exercise 2.59): the expectation
`⟪X⟫ = ⟨0|X|0⟩` vanishes. -/
theorem expectation_pauliX_qubitBasis_zero :
    (qubitBasis 0).expectation pauliXObservable = 0 := sorry

/-- **Standard deviation of `X` in `|0⟩` is `1`** (Nielsen & Chuang, Exercise 2.59):
`Δ(X) = 1`. -/
theorem stdDev_pauliX_qubitBasis_zero :
    (qubitBasis 0).stdDev pauliXObservable = 1 := sorry

end AxQM
