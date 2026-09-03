/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit

/-!
# An exponential tail bound for the random-sampling error test

Fix a ground set `S` of `2 * n` bits and an error set `E ⊆ S` (`|E| = M` errors). A random
`n`-element subset `C ⊆ S` is used as *check bits*.

## Main results

* `Finset.card_powersetCard_filter_inter_lt_and_lt_div_choose_le_two_pow`: an exponential bound for
  the event `{(C ∩ E).card < s ∧ t < (E \ C).card}` — few errors on the check bits *and* many on
  the untested rest.
-/

open Finset

namespace Finset

public section

variable {α : Type*} [DecidableEq α]

/-- **Random-sampling error bound for the full BB84 test event** (Nielsen & Chuang, Exercise
12.27). The exponential bound `p ≤ (2 n + 1) * 2 ^ (-ε² n / 4)` holds for the full event of the
exercise — *fewer than `s` errors on the check bits `C`* **and** *more than `t` errors on the
untested rest `S \ C`*.

Here `(E \ C).card` counts errors on the untested bits `S \ C` (as `E ⊆ S`), which is the
exercise's count of more than `(δ + ε) n` errors among the remaining `n` bits. -/
theorem card_powersetCard_filter_inter_lt_and_lt_div_choose_le_two_pow {n : ℕ} (S E : Finset α)
    (s t : ℕ) (ε : ℝ) (hS : S.card = 2 * n) (hE : E ⊆ S) (hs : 1 ≤ s) (hε : 0 ≤ ε)
    (hgap : ε * n ≤ (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ)) :
    (((S.powersetCard n).filter
        (fun C => (C ∩ E).card < s ∧ t < (E \ C).card)).card : ℝ) / ((2 * n).choose n)
      ≤ (2 * n + 1) * (2 : ℝ) ^ (-(ε ^ 2 * n) / 4) := sorry

end

end Finset
