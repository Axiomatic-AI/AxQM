/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The binary entropy function measured in bits

Mathlib's `Real.binEntropy` measures the Shannon entropy of a Bernoulli random variable in *nats*,
using the natural logarithm; its maximum value is therefore `Real.log 2`. In much of the
information-theory literature (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
being one example) entropy is measured in *bits*, using the base-`2` logarithm, so that a fair coin
has entropy exactly `1`.

## Main declarations

* `Real.binEntropyBit`: the binary entropy function measured in bits,
  `binEntropyBit p := -(p * logb 2 p) - (1 - p) * logb 2 (1 - p)`.

## Main results

* `Real.binEntropyBit_two_inv`: `binEntropyBit (1 / 2) = 1` (a fair coin carries one bit).
* `Real.isGreatest_range_binEntropyBit`: `1` is the greatest value of `binEntropyBit`.
* `Real.strictConcaveOn_binEntropyBit`: `binEntropyBit` is strictly concave on `[0, 1]`.
* `Real.concaveOn_binEntropyBit`: `binEntropyBit` is concave on `[0, 1]` (inequality (11.11) of
  Nielsen & Chuang, Exercise 11.4).
-/

open Set

namespace Real

public section

variable {p : ℝ}

/-- The **binary entropy function measured in bits**. It is the version of `Real.binEntropy` in
which a fair coin carries exactly one bit of entropy. -/
@[pp_nodot] noncomputable def binEntropyBit (p : ℝ) : ℝ :=
  -(p * logb 2 p) - (1 - p) * logb 2 (1 - p)

/-- A fair coin (`p = 1 / 2`) carries exactly one bit of entropy:
`binEntropyBit (1 / 2) = 1`. -/
@[simp] lemma binEntropyBit_two_inv : binEntropyBit 2⁻¹ = 1 := sorry

/-- **The binary entropy function, measured in bits, attains its maximum value of one.** `1` is the
greatest value taken by `binEntropyBit`. -/
theorem isGreatest_range_binEntropyBit : IsGreatest (range binEntropyBit) 1 := sorry

/-- **The binary entropy in bits is strictly concave** on `[0, 1]`. Equivalently, the concavity
inequality is an equality only in the trivial cases `x = y`, `a = 0`, or `b = 0` — the precise
content of Nielsen & Chuang, Exercise 11.4. -/
theorem strictConcaveOn_binEntropyBit : StrictConcaveOn ℝ (Icc 0 1) binEntropyBit := sorry

/-- **The binary entropy in bits is concave** on `[0, 1]`. -/
theorem concaveOn_binEntropyBit : ConcaveOn ℝ (Icc 0 1) binEntropyBit := sorry

end

end Real
