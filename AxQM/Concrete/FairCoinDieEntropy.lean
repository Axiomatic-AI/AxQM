/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# AxQM.Concrete — Shannon entropy of a fair coin and a fair die

The concrete distributions and entropy computations of Nielsen & Chuang Exercise 11.1
("Simple calculations of entropy", p. 501):

## Contents

* `fairCoin` / `fairDie` — the uniform distributions on `Fin 2` / `Fin 6`, together with the basic
  probability facts (nonnegativity and normalisation to `1`).
* `entropy_fairCoin_div_log_two` / `entropy_fairDie_div_log_two` — **the two calculations**, in
  *bits* (Mathlib's `Real.entropy` uses the natural logarithm, so these divide by `log 2`, the
  convention N&C uses): `1` bit for the coin and `log₂ 6 ≈ 2.585` bits for the die.
* `entropy_lt_entropy_fairCoin_of_ne_uniform` / `entropy_lt_entropy_fairDie_of_ne_uniform` — the
  **unfair** case: **an unfair coin/die has strictly less entropy than the fair one**.
-/

open scoped BigOperators

namespace AxQM.Concrete

noncomputable section

-- The uniform distributions are written with `Function.const` rather than `fun _ => c`: both denote
-- the same constant function, but `Function.const` keeps the index argument syntactically present,
-- which is what the `unusedArguments` linter requires of a top-level `def` (a bare `fun _ => c`
-- beta-reduces the index away and is flagged). Do not "simplify" these back to `fun _ => c`.

/-- The **fair-coin** distribution: the uniform probability distribution on the two outcomes
`Fin 2`, each with probability `1/2`. -/
def fairCoin : Fin 2 → ℝ := Function.const _ (2 : ℝ)⁻¹

/-- The **fair-die** distribution: the uniform probability distribution on the six outcomes
`Fin 6`, each with probability `1/6`. -/
def fairDie : Fin 6 → ℝ := Function.const _ (6 : ℝ)⁻¹

/-- **Entropy of a fair coin (bits).** In the base-2 convention N&C uses (bit-entropy is
`Real.entropy p / Real.log 2`), a fair coin carries exactly `1` bit of entropy. -/
theorem entropy_fairCoin_div_log_two : Real.entropy fairCoin / Real.log 2 = 1 := sorry

/-- **Entropy of a fair die (bits).** In the base-2 convention N&C uses, a fair die carries
`Real.logb 2 6 = log₂ 6 ≈ 2.585` bits of entropy. -/
theorem entropy_fairDie_div_log_two : Real.entropy fairDie / Real.log 2 = Real.logb 2 6 := sorry

/-- **An unfair coin carries strictly less entropy than a fair one.** Any distribution on the two
outcomes `Fin 2` other than `fairCoin` has Shannon entropy strictly below that of the fair coin
(`log 2`, i.e. `1` bit). This is the coin case of N&C's "unfair" discussion. -/
theorem entropy_lt_entropy_fairCoin_of_ne_uniform {p : Fin 2 → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hne : p ≠ fairCoin) :
    Real.entropy p < Real.entropy fairCoin := sorry

/-- **An unfair die carries strictly less entropy than a fair one.** Any distribution on the six
outcomes `Fin 6` other than `fairDie` has Shannon entropy strictly below that of the fair die
(`log 6`, i.e. `log₂ 6` bits). This is the die case of N&C's "unfair" discussion. -/
theorem entropy_lt_entropy_fairDie_of_ne_uniform {p : Fin 6 → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hne : p ≠ fairDie) :
    Real.entropy p < Real.entropy fairDie := sorry

end

end AxQM.Concrete
