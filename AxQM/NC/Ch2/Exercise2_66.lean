/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellState

/-!
# Nielsen & Chuang, Exercise 2.66

*(N&C p. 94.)*

Show average value of X1 Z2 for two-qubit state (|00>+|11>)/sqrt2 is zero.

* `bellPhiPlus_expectation_pauliX_tmul_pauliZ_eq_zero`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.66.** The average value of the observable `X₁Z₂ = X ⊗ Z` in the
Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` is zero: `⟪X ⊗ Z⟫_{Φ⁺} = 0`. -/
theorem bellPhiPlus_expectation_pauliX_tmul_pauliZ_eq_zero :
    bellPhiPlus.expectation (pauliXObservable ⊗ pauliZObservable) = 0 := sorry

end AxQM
