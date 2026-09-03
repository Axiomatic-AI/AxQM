/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropy
public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
public import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality

/-!
# Concavity of the Shannon entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 11.21 asks for the
concavity of the Shannon entropy.

## Main results

* `Real.sum_mul_entropy_le_entropy_convexCombination`: **concavity of the Shannon entropy**
  (Nielsen & Chuang, Exercise 11.21) — `∑ᵢ pᵢ H(qᵢ) ≤ H(∑ᵢ pᵢ qᵢ)` for probability distributions
  `qᵢ` weighted by a probability distribution `p`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Real

/-- **Concavity of the Shannon entropy** (Nielsen & Chuang, Exercise 11.21). For a probability
distribution `p : ι → ℝ` and a family of probability distributions `q : ι → α → ℝ`,
```
∑ᵢ pᵢ H(qᵢ) ≤ H(∑ᵢ pᵢ qᵢ),
```
the weighted average of the entropies is at most the entropy of the mixture.
-/
theorem sum_mul_entropy_le_entropy_convexCombination {ι α : Type*} [Fintype ι] [Fintype α]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    {q : ι → α → ℝ} (hq : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1) :
    ∑ i, p i * Real.entropy (q i) ≤ Real.entropy (fun a => ∑ i, p i * q i a) := sorry

end Real
