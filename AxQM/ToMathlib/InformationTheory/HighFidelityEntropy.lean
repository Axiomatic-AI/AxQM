/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit

/-!
# The spike-distribution entropy behind "high fidelity implies low entropy"

Nielsen & Chuang's Lemma 12.19 (*Quantum Computation and Quantum Information*, §12.6.5, p. 594)
states that if a density matrix `ρ` on `2n` qubits has squared fidelity greater than `1 - 2^(-s)`
with a target pure state, then its von Neumann entropy is small:
`S(ρ) < (2n + s + 1 / ln 2) · 2^(-s) + O(2^(-2s))`.  This file concerns the entropy of the
**spike** distribution appearing in that bound: a single mass `1 - 2^(-s)` with the residual
weight `2^(-s)` spread uniformly over `2^(2n) - 1` further outcomes.  Its base-`2` entropy is
the right-hand side of N&C eq. (12.199).

## Main declarations

* `Real.spikeEntropyBit s n`: the base-`2` Shannon entropy of the spike distribution, i.e. the
  right-hand side of N&C eq. (12.199).

## Main results

* `Real.spikeEntropyBit_lt`: the clean strict bound matching Lemma 12.19's expression,
  `spikeEntropyBit s n < (2n + s + 1 / ln 2) · 2^(-s)` for `0 < s` and `1 ≤ n`, without the
  `O(2^(-2s))` remainder of the textbook statement.
-/

open Real

@[expose] public section

namespace Real

variable (s : ℝ) (n : ℕ)

/-- The base-`2` Shannon entropy of the **spike distribution** from the proof of Nielsen & Chuang's
Lemma 12.19: a peak of probability `1 - 2^(-s)` on one outcome, with the residual mass `2^(-s)`
spread uniformly over the other `2^(2n) - 1` outcomes.  This is the right-hand side of N&C eq.
(12.199). -/
noncomputable def spikeEntropyBit : ℝ :=
  -(1 - (2 : ℝ) ^ (-s)) * Real.logb 2 (1 - (2 : ℝ) ^ (-s))
    - (2 : ℝ) ^ (-s) * Real.logb 2 ((2 : ℝ) ^ (-s) / ((2 : ℝ) ^ (2 * n) - 1))

/-- **Exercise 12.30 (the bound of Lemma 12.19).**  For `0 < s` and `1 ≤ n`, the strict inequality
`spikeEntropyBit s n < (2n + s + 1 / ln 2) · 2^(-s)` — exactly the expression stated in
Lemma 12.19, without the textbook's `O(2^(-2s))` slack. -/
theorem spikeEntropyBit_lt (hs : 0 < s) (hn : 1 ≤ n) :
    spikeEntropyBit s n < (2 * n + s + 1 / Real.log 2) * (2 : ℝ) ^ (-s) := sorry

end Real
