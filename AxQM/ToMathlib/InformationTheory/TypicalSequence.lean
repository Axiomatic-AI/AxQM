/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# The theorem of typical sequences (classical asymptotic equipartition property)

For a finite alphabet `α`, a probability mass function `p : α → ℝ` (`0 ≤ p x`, `∑ x, p x = 1`) and a
tolerance `ε`, a length-`n` sequence `s : Fin n → α` is **`ε`-typical** when its `n`-fold i.i.d.
product probability `∏ i, p (s i)` is squeezed between `exp (-n (H + ε))` and `exp (-n (H - ε))`,
where `H = Real.entropy p` is the Shannon entropy (in nats). This is Nielsen & Chuang's primary
definition (their Eq. 12.26), the natural-logarithm form of `2^{-n(H+ε)} ≤ p ≤ 2^{-n(H-ε)}` (the
base-`2` version is the same statement rescaled).

## Main results

- `Real.typicalSeq`: the `ε`-typical set (Eq. 12.26).
- `Real.exists_le_sum_typicalSeq`: **part (1), Nielsen–Chuang form** — for any `δ > 0`, for all
  sufficiently large `n`, that probability is at least `1 - δ`.
- `Real.exists_card_typicalSeq_bounds`: **part (2), Nielsen–Chuang form** — for any `δ > 0`, for all
  sufficiently large `n`, both cardinality bounds of Eq. 12.28 hold.
- `Real.exists_sum_prod_le_of_card_le_exp`: **part (3), the small-set bound** (Eq. 12.29) — for
  `R < H`, `δ > 0`, large `n`, *every* collection `S` with `|S| ≤ exp (n R)` carries total
  probability `∑ s ∈ S, ∏ p ≤ δ`.
-/

@[expose] public section

open Finset

namespace Real

variable {α : Type*} [Fintype α]

open Classical in
/-- The set `T(n, ε)` of **`ε`-typical** length-`n` sequences for the i.i.d. source `p` (Nielsen &
Chuang, Eq. 12.26). The lower bound being a positive exponential, this automatically excludes
zero-probability sequences. -/
noncomputable def typicalSeq (p : α → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  univ.filter fun s => Real.exp (-(n : ℝ) * (entropy p + ε)) ≤ ∏ i, p (s i) ∧
    ∏ i, p (s i) ≤ Real.exp (-(n : ℝ) * (entropy p - ε))

/-- **Nielsen & Chuang, Theorem 12.2 (1), Nielsen–Chuang form.** Fix `ε > 0`. For any `δ > 0`, for
all sufficiently large `n`, the probability that a sequence is `ε`-typical is at least
`1 - δ`. -/
theorem exists_le_sum_typicalSeq {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, 1 - δ ≤ ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) := sorry

/-- **Nielsen & Chuang, Theorem 12.2 (2), Nielsen–Chuang form** (Eq. 12.28). Fix `ε > 0`. For any `δ
> 0`, for all sufficiently large `n`, the number of `ε`-typical sequences satisfies `(1 - δ) exp
(n (H - ε)) ≤ |T(n, ε)| ≤ exp (n (H + ε))`. -/
theorem exists_card_typicalSeq_bounds {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      (1 - δ) * Real.exp (n * (entropy p - ε)) ≤ ((typicalSeq p n ε).card : ℝ) ∧
        ((typicalSeq p n ε).card : ℝ) ≤ Real.exp (n * (entropy p + ε)) := sorry

/-- **Nielsen & Chuang, Theorem 12.2 (3)** (Eq. 12.29, the small-set bound). Fix a rate `R` strictly
below the entropy (`R < entropy p`). For any `δ > 0`, for all sufficiently large `n`, *every*
collection `S` of length-`n` sequences with at most `exp (n R)` members carries total
probability at most `δ`: `∑ s ∈ S, ∏ i, p (s i) ≤ δ`. -/
theorem exists_sum_prod_le_of_card_le_exp {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR : R < entropy p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ S : Finset (Fin n → α),
      (S.card : ℝ) ≤ Real.exp (n * R) → ∑ s ∈ S, ∏ i, p (s i) ≤ δ := sorry

end Real
