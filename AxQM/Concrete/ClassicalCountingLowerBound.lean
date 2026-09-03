/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalCountingEstimator
import Mathlib.MeasureTheory.Measure.Real

/-!
# Concrete: the classical counting estimator needs `k = Ω(N)` samples (N&C Exercise 6.13)

Nielsen & Chuang, Exercise 6.13 (p. 261) asks, for the classical sampling counting estimator
`S ≡ N · (∑ⱼ Xⱼ) / k`, for a lower bound: estimating the solution count `M` to accuracy `√M` with
probability ≥ 3/4 for all `M` requires `Ω(N)` classical oracle calls.

## Results

* `samplingEstimator_needs_linear_samples` — **Exercise 6.13 (`k = Ω(N)`)**: if for every
  `M ∈ [1, N−1]` the estimator is within `√M` of `M` with probability at least `3/4`, then
  `N < 4·k`.
-/

open MeasureTheory
open scoped BigOperators

namespace AxQM.Concrete

/-- **Exercise 6.13 (`k = Ω(N)`).** If the classical sampling counting estimator estimates every
`M ∈ [1, N−1]` to within `√M` with probability at least `3/4`, then `N < 4·k` — i.e. the number of
samples must be `k > N/4 = Ω(N)`. -/
theorem samplingEstimator_needs_linear_samples {N k : ℕ} (hk : 0 < k)
    (hacc : ∀ M : ℕ, 1 ≤ M → M ≤ N - 1 →
      3 / 4 ≤ (sampleSpaceMeasure N M k).real
        {ω | |samplingEstimator N k ω - (M : ℝ)| ≤ Real.sqrt (M : ℝ)}) :
    N < 4 * k := sorry

end AxQM.Concrete
