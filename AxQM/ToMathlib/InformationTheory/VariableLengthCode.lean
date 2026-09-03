/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.TypicalSequence

/-!
# Variable-length zero-error data compression (Nielsen & Chuang, Exercise 12.5)

Nielsen & Chuang's Exercise 12.5 asks to turn a *heuristic* variable-length compression scheme into
a rigorous argument: an i.i.d. source with entropy rate `H(X)` can be compressed to an **average of
`R` bits per source symbol, for any `R > H(X)`, with zero probability of error**. The heuristic:
encode a length-`n` block `x` by first testing whether it is `ε`-typical; if so send a short index
(`⌈log₂ |T(n, ε)|⌉` bits) into the typical set, otherwise send an uncompressed index
(`⌈log₂ dⁿ⌉` bits, `d = |α|`). A leading flag bit records which branch was taken, so the code is
losslessly (zero-error) decodable.

## Main definitions

- `Real.binBlockCode`: the reusable **fixed-length binary block code** — an injective map from any
  finite type of at most `2 ^ w` elements into the length-`w` binary strings `Fin w → Bool`.
- `Real.typicalWidth` / `Real.atypicalWidth`: the two codeword body widths `⌈log₂ |T(n, ε)|⌉` and
  `⌈log₂ dⁿ⌉`.
- `Real.typicalCode`: the variable-length encoder `(Fin n → α) → List Bool` of the heuristic.
-/

@[expose] public section

open Finset

namespace Real

variable {α : Type*} [Fintype α]

/-- **Fixed-length binary block code.** A finite type `β` with at most `2 ^ w` elements embeds
injectively into the length-`w` binary strings `Fin w → Bool` (there are `2 ^ w` of them).
Noncomputable, as it merely selects *some* injection via cardinality. -/
noncomputable def binBlockCode (β : Type*) [Fintype β] {w : ℕ}
    (h : Fintype.card β ≤ 2 ^ w) : β ↪ (Fin w → Bool) :=
  Classical.choice <| Function.Embedding.nonempty_iff_card_le.mpr <| by
    rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The number of bits used to index the `ε`-typical sequences: `⌈log₂ |T(n, ε)|⌉`. -/
noncomputable def typicalWidth (p : α → ℝ) (n : ℕ) (ε : ℝ) : ℕ :=
  Nat.clog 2 (typicalSeq p n ε).card

/-- The number of bits used to index an arbitrary length-`n` sequence uncompressed. -/
noncomputable def atypicalWidth (α : Type*) [Fintype α] (n : ℕ) : ℕ :=
  Nat.clog 2 (Fintype.card (Fin n → α))

/-- The `ε`-typical set has at most `2 ^ typicalWidth` elements, so it embeds into
`typicalWidth`-bit codewords. -/
theorem card_typicalSeq_le_two_pow_typicalWidth (p : α → ℝ) (n : ℕ) (ε : ℝ) :
    Fintype.card (typicalSeq p n ε) ≤ 2 ^ typicalWidth p n ε := by
  rw [Fintype.card_coe, typicalWidth]
  exact Nat.le_pow_clog one_lt_two _

/-- There are at most `2 ^ atypicalWidth` length-`n` sequences, so they embed into
`atypicalWidth`-bit codewords. -/
theorem card_le_two_pow_atypicalWidth (n : ℕ) :
    Fintype.card (Fin n → α) ≤ 2 ^ atypicalWidth α n := by
  rw [atypicalWidth]
  exact Nat.le_pow_clog one_lt_two _

open Classical in
/-- **The variable-length zero-error compression code of Nielsen & Chuang, Exercise 12.5.** A
length-`n` block `x` is encoded as a leading flag bit followed by a fixed-length index:

* if `x` is `ε`-typical, the flag `false` followed by a `typicalWidth`-bit index into `T(n, ε)`;
* otherwise the flag `true` followed by an `atypicalWidth`-bit uncompressed index of `x`.

The flag bit lets the decoder tell the two branches apart, making the code losslessly decodable.
Noncomputable, inheriting the block-code choice from `binBlockCode`. -/
noncomputable def typicalCode (p : α → ℝ) (n : ℕ) (ε : ℝ) (x : Fin n → α) : List Bool :=
  if h : x ∈ typicalSeq p n ε then
    false :: List.ofFn (binBlockCode _ (card_typicalSeq_le_two_pow_typicalWidth p n ε) ⟨x, h⟩)
  else
    true :: List.ofFn (binBlockCode _ (card_le_two_pow_atypicalWidth n) x)

open Classical in
/-- **Nielsen & Chuang, Exercise 12.5 (variable-length zero-error data compression).** For any rate
`R` strictly above the base-2 entropy `H(X) = entropy p / log 2` — equivalently
`entropy p < log 2 · R` — there is a typical-set width `ε > 0` and a block length `N` such that for
all `n ≥ N` the variable-length code `typicalCode p n ε`

* is **injective**, hence decodable with **zero probability of error**, and
* compresses the i.i.d. source `p` to an average of at most `R` bits per source symbol:
  `∑ₓ pⁿ(x) · (len x) ≤ n · R`, where `pⁿ(x) = ∏ᵢ p(xᵢ)` is the i.i.d. block probability.

This turns Nielsen & Chuang's heuristic into a rigorous statement. -/
theorem exists_typicalCode_expectedLength_le {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR : entropy p < Real.log 2 * R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      Function.Injective (typicalCode p n ε) ∧
        (∑ x, (∏ i, p (x i)) * ((typicalCode p n ε x).length : ℝ)) ≤ (n : ℝ) * R := sorry

end Real
