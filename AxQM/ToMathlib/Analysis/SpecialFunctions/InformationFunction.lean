/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Axiomatic characterization of the information function

An *information function* `I : ℝ → ℝ` assigns to an event of probability `p` a number `I p`
measuring "how much information" the event's occurrence conveys (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 11.2, p. 501).

## Main results

* `Real.exists_const_mul_log_of_map_mul_eq_add`: a differentiable function on the positive reals
  satisfying `I (p * q) = I p + I q` equals `k * Real.log` for some constant `k`.
* `Real.sum_mul_eq_neg_mul_entropy_of_eq_const_mul_log`: consequently the average information gain
  `∑ i, p i * I (p i)` over a distribution `p` with `I p = k * Real.log p` equals `-k` times the
  Shannon entropy `Real.entropy p`, exhibiting the Shannon entropy as the essentially unique such
  average measure of information.
-/

open Set Filter Topology

namespace Real

public section

/-- **Cauchy's logarithmic functional equation.** A function `I : ℝ → ℝ` that is differentiable at
every positive real and satisfies `I (p * q) = I p + I q` for all `p, q > 0` is a constant
multiple of the logarithm. -/
theorem exists_const_mul_log_of_map_mul_eq_add {I : ℝ → ℝ}
    (hdiff : ∀ x, 0 < x → DifferentiableAt ℝ I x)
    (hmul : ∀ p q, 0 < p → 0 < q → I (p * q) = I p + I q) :
    ∃ k, ∀ p, 0 < p → I p = k * Real.log p := sorry

/-- Given an information function of the form `I p = k * Real.log p` on the positive reals, the
average information gained from a distribution `p` — the expectation `∑ i, p i * I (p i)` —
equals `-k` times the Shannon entropy `Real.entropy p`. -/
theorem sum_mul_eq_neg_mul_entropy_of_eq_const_mul_log {ι : Type*} [Fintype ι]
    {I : ℝ → ℝ} {k : ℝ} (hI : ∀ p, 0 < p → I p = k * Real.log p)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    ∑ i, p i * I (p i) = -k * Real.entropy p := sorry

end

end Real
