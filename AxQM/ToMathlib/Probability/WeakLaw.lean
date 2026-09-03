/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Probability.IdentDistrib

/-!
# The weak law of large numbers

For pairwise independent, identically distributed, square-integrable real random variables, the
sample average converges to the common mean in probability (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, Theorem 12.3, Box 12.3).

## Main results

* `ProbabilityTheory.tendsto_meas_abs_sum_range_div_sub_gt`: the same result in the literal form of
  N&C Theorem 12.3, `p(|Sₙ - 𝔼[X 0]| > ε) → 0` for every `ε > 0`.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Weak law of large numbers, literal N&C form** (Nielsen & Chuang, Theorem 12.3). For pairwise
independent, identically distributed, square-integrable real random variables `X`, for every
`ε > 0` the probability that the sample average `Sₙ = (∑ i ∈ range n, X i) / n` deviates from the
common mean `𝔼[X 0]` by more than `ε` tends to `0`, i.e. `p(|Sₙ - 𝔼[X 0]| > ε) → 0`. -/
theorem tendsto_meas_abs_sum_range_div_sub_gt [IsProbabilityMeasure μ] (hℒp : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε < |(∑ i ∈ range n, X i ω) / n - ∫ x, X 0 x ∂μ|}) atTop (nhds 0) :=
      sorry

end ProbabilityTheory
