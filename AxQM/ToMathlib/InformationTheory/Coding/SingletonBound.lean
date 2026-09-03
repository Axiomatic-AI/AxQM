/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Singleton bound for linear codes

For a linear `[n, k, d]` code — block length `n = #ι`, dimension `k = Module.finrank K C`, and
minimum distance `d = LinearCode.minDist C` — the **Singleton bound** states that
`n − k ≥ d − 1`, equivalently `d ≤ n − k + 1` (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Exercise 10.21, p. 449).

## Main results

* `LinearCode.singleton_bound`: **the Singleton bound**, `d(C) ≤ n − k + 1`, for any nontrivial code
  `C ≠ ⊥` (N&C Exercise 10.21).
-/

@[expose] public section

namespace LinearCode

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K]

/-- **The Singleton bound** (Nielsen & Chuang, Exercise 10.21, p. 449). A nontrivial linear
`[n, k, d]` code satisfies `d ≤ n − k + 1`, i.e. `n − k ≥ d − 1`, where `n = #ι` is the block
length, `k = Module.finrank K C` the dimension, and `d = minDist C` the minimum distance.

The hypothesis `C ≠ ⊥` rules out the trivial code `{0}`, which has no finite minimum distance (no
nonzero codeword) and so no `[n, k, d]` parameters. For any nontrivial code the minimum distance is
a genuine natural number `1 ≤ d ≤ n`. -/
theorem singleton_bound (C : LinearCode K ι) (hC : C ≠ ⊥) :
    minDist C ≤ (Fintype.card ι - Module.finrank K C + 1 : ℕ) := sorry

end LinearCode
