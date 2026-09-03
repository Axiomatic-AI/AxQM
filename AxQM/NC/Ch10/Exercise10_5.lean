/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorPhaseSyndrome

/-!
# Nielsen & Chuang, Exercise 10.5 — the Shor-code phase-flip syndrome

*(N&C p. 433.)*

Shor code phase-flip syndrome corresponds to measuring X1X2X3X4X5X6 and X4X5X6X7X8X9.

* `shorPhaseSyndromeX123456_hasEigenstate_shorCatProduct` — `X₁X₂X₃X₄X₅X₆` is an eigen-observable
  with eigenvalue `(−1)^{σ₁+σ₂}`.
* `shorPhaseSyndromeX456789_hasEigenstate_shorCatProduct` — `X₄X₅X₆X₇X₈X₉` is an eigen-observable
  with eigenvalue `(−1)^{σ₂+σ₃}`.
-/

noncomputable section

namespace AxQM

/-- **Exercise 10.5 — `X₁X₂X₃X₄X₅X₆` compares the signs of blocks 1 and 2.** On a three-block
product of sign-definite cat states, `X₁X₂X₃X₄X₅X₆` acts as the observable with eigenvalue
`(−1)^{σ₁+σ₂}`: measuring it yields `+1` iff the first two blocks have the same sign and `−1` iff
they differ. This is the first half of the phase-flip syndrome measurement. -/
theorem shorPhaseSyndromeX123456_hasEigenstate_shorCatProduct (σ₁ σ₂ σ₃ : Fin 2) :
    shorPhaseSyndromeX123456.HasEigenstate ((-1 : ℝ) ^ ((σ₁ : ℕ) + (σ₂ : ℕ)))
      (shorCatProduct σ₁ σ₂ σ₃) := sorry

/-- **Exercise 10.5 — `X₄X₅X₆X₇X₈X₉` compares the signs of blocks 2 and 3.** On a three-block
product of sign-definite cat states, `X₄X₅X₆X₇X₈X₉` acts as the observable with eigenvalue
`(−1)^{σ₂+σ₃}`: measuring it yields `+1` iff the last two blocks have the same sign and `−1` iff
they differ. This is the second half of the phase-flip syndrome measurement. -/
theorem shorPhaseSyndromeX456789_hasEigenstate_shorCatProduct (σ₁ σ₂ σ₃ : Fin 2) :
    shorPhaseSyndromeX456789.HasEigenstate ((-1 : ℝ) ^ ((σ₂ : ℕ) + (σ₃ : ℕ)))
      (shorCatProduct σ₁ σ₂ σ₃) := sorry

end AxQM
