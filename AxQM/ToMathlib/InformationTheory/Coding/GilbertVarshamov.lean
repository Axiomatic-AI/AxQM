/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.LinearCode
public import AxQM.ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-!
# The Gilbert–Varshamov existence bound for binary linear codes

The **Gilbert–Varshamov bound** guarantees the existence of good linear codes: a binary linear code
of block length `n`, dimension at least `k`, and minimum distance at least `d` exists as long as the
Hamming-ball volume `∑_{i < d} C(n, i)` does not exceed `2 ^ (n - k)` (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, §10.4.1 eq. (10.63) and Exercise 10.23).

## Main results

* `LinearCode.exists_correctsErrors_of_rate_le`: the **entropy (rate) form** of the classical
  Gilbert–Varshamov bound (N&C Exercise 10.23, eq. (10.63)). In the regime `4t ≤ n`, if the target
  rate obeys `k ≤ n · (1 - H₂(2t/n))` (i.e. `k/n ≥ 1 - H₂(2t/n)`), then a binary linear code of
  dimension at least `k` correcting `t` errors exists.
-/

open Finset Matrix

public section

variable {n : ℕ}

namespace LinearCode

/-- **Classical Gilbert–Varshamov bound, entropy (rate) form** (Nielsen & Chuang, Exercise 10.23,
eq. (10.63)).

This is the achievability content of the classical bound: good codes of rate up to `1 -
H₂(2t/n)` exist.
-/
theorem exists_correctsErrors_of_rate_le {n k t : ℕ} (h4t : 4 * t ≤ n)
    (hrate : (k : ℝ) ≤ n * (1 - Real.binEntropyBit (2 * t / n))) :
    ∃ C : LinearCode (ZMod 2) (Fin n),
      k ≤ Module.finrank (ZMod 2) C ∧ CorrectsErrors C t := sorry

end LinearCode

end
