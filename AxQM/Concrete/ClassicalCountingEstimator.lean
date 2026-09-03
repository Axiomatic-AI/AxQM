/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Probability.Distributions.TwoValued
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Concrete: standard deviation of the classical sampling counting estimator (N&C Exercise 6.13)

Nielsen & Chuang, Exercise 6.13 (p. 261) studies the *classical* algorithm for the counting
problem: to estimate the number `M` of solutions among `N` items, sample `k` items uniformly and
independently, let `Xⱼ = 1` if the `j`-th sample is a solution and `Xⱼ = 0` otherwise, and return
the estimator `S ≡ N ∑ⱼ Xⱼ / k`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace AxQM.Concrete

/-- The Bernoulli success probability `p = M/N`, clamped to `[0,1]` so the definitions require no
hypothesis. -/
noncomputable def samplingProb (N M : ℕ) : ℝ≥0 := min ((M : ℝ≥0) / (N : ℝ≥0)) 1

/-- `samplingProb` is at most `1` (it is a probability). -/
lemma samplingProb_le_one (N M : ℕ) : samplingProb N M ≤ 1 := min_le_right _ _

/-- The single-sample `Bernoulli(p)` measure on `Bool`. -/
noncomputable def sampleMeasure (N M : ℕ) : Measure Bool :=
  (PMF.bernoulli (samplingProb N M) (samplingProb_le_one N M)).toMeasure

/-- The product measure of `k` i.i.d. `Bernoulli(M/N)` samples on `Fin k → Bool`. -/
noncomputable def sampleSpaceMeasure (N M k : ℕ) : Measure (Fin k → Bool) :=
  Measure.pi (fun _ : Fin k => sampleMeasure N M)

/-- The indicator random variable `Xᵢ` : `1` if the `i`-th sample is a solution, else `0`. -/
def sampleIndicator (k : ℕ) (i : Fin k) : (Fin k → Bool) → ℝ := fun ω => bif ω i then 1 else 0

/-- The estimator `S = (N/k) · ∑ᵢ Xᵢ` (N&C's `S ≡ N ∑ⱼ Xⱼ / k`). -/
noncomputable def samplingEstimator (N k : ℕ) : (Fin k → Bool) → ℝ :=
  ((N : ℝ) / (k : ℝ)) • ∑ i : Fin k, sampleIndicator k i

/-- The standard deviation `ΔS` of the sampling estimator. -/
noncomputable def samplingEstimatorStddev (N M k : ℕ) : ℝ :=
  Real.sqrt (variance (samplingEstimator N k) (sampleSpaceMeasure N M k))

/-- **Exercise 6.13 (standard deviation).** The standard deviation of the classical sampling
counting estimator is `ΔS = √(M(N−M)/k)`. -/
theorem samplingEstimatorStddev_eq {N M k : ℕ} (hM : M ≤ N) (hN : 0 < N) (hk : 0 < k) :
    samplingEstimatorStddev N M k = Real.sqrt ((M : ℝ) * ((N : ℝ) - M) / k) := sorry

end AxQM.Concrete
