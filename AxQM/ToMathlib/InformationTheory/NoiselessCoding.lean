/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.TypicalSequence

/-!
# Shannon's noiseless channel coding theorem (data compression)

For a finite alphabet `α` and an i.i.d. classical information source with probability mass function
`p : α → ℝ` (`0 ≤ p x`, `∑ x, p x = 1`), a **rate-`R` compression scheme** at block length `n`
compresses a source sequence `x : Fin n → α` into a bit string of length `⌊n R⌋` and decompresses
it back to a sequence. Following Nielsen & Chuang (p. 540) we model such a scheme as the structure
`CompressionScheme`.

## Main results (this file)

- `Real.CompressionScheme`: the encode/decode model of a rate-`R` scheme (Nielsen & Chuang, `Cₙ`,
  `Dₙ`).
- `Real.CompressionScheme.successProb`: the exact-recovery probability `p(Dₙ(Cₙ(x)) = x)`.
- `Real.exists_reliable_compressionScheme`: **Theorem 12.4, direct part.** If
  `entropy p < R log 2` then a reliable rate-`R` compression scheme family exists — its success
  probability tends to `1`.
- `Real.not_reliable_compressionScheme`: **Theorem 12.4, converse.** Under the same hypotheses no
  rate-`R` scheme family is reliable (the success probability does not tend to `1`).
-/

@[expose] public section

open Finset Filter Topology

namespace Real

variable {α : Type*} [Fintype α]

/-- A **rate-`R` compression scheme** for a length-`n` source over the alphabet `α`
(Nielsen & Chuang, p. 540): an `encode` (their `Cₙ`) mapping a source sequence `x : Fin n → α` to a
`numBits`-bit string, and a matching `decode` (their `Dₙ`) mapping bit strings back to sequences.
The intended block-length dependence is `numBits = ⌊n R⌋`, so the compressed space carries `⌊n R⌋`
bits per block. -/
structure CompressionScheme (α : Type*) (n numBits : ℕ) where
  /-- The compression map `Cₙ`: a source sequence is compressed to a `numBits`-bit string. -/
  encode : (Fin n → α) → (Fin numBits → Bool)
  /-- The decompression map `Dₙ`: a `numBits`-bit string is decompressed back to a source
  sequence. -/
  decode : (Fin numBits → Bool) → (Fin n → α)

open Classical in
/-- The **success probability** of a compression scheme under the i.i.d. product distribution `p`:
the total probability of the source sequences `x` that are recovered exactly,
`decode (encode x) = x`. This is Nielsen & Chuang's `p(Dₙ(Cₙ(x)) = x)`. -/
noncomputable def CompressionScheme.successProb (p : α → ℝ) {n numBits : ℕ}
    (sch : CompressionScheme α n numBits) : ℝ :=
  ∑ x ∈ univ.filter (fun x => sch.decode (sch.encode x) = x), ∏ i, p (x i)

/-- **Nielsen & Chuang, Theorem 12.4 — direct part (achievability).** If the rate exceeds the
entropy rate, `entropy p < R * Real.log 2` (i.e. `R > H(X)` in bits), then a **reliable**
rate-`R` compression scheme family exists: a family `sch n : CompressionScheme α n ⌊n R⌋` whose
success probability tends to `1` as `n → ∞`. -/
theorem exists_reliable_compressionScheme (p : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR : entropy p < R * Real.log 2) :
    ∃ sch : (n : ℕ) → CompressionScheme α n ⌊(n : ℝ) * R⌋₊,
      Tendsto (fun n => (sch n).successProb p) atTop (𝓝 1) := sorry

/-- **Nielsen & Chuang, Theorem 12.4 — converse.** For a genuine nonnegative bit-rate below the
entropy rate — `0 ≤ R` and `R * Real.log 2 < entropy p` (i.e. `R < H(X)` in bits) — *no*
rate-`R` compression scheme family is **reliable**: the success probability does not tend to
`1`, exactly N&C's "any compression scheme will not be reliable".
-/
theorem not_reliable_compressionScheme (p : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R * Real.log 2 < entropy p)
    (sch : (n : ℕ) → CompressionScheme α n ⌊(n : ℝ) * R⌋₊) :
    ¬ Tendsto (fun n => (sch n).successProb p) atTop (𝓝 1) := sorry

end Real
