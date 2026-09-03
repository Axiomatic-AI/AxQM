/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.DataProcessingInequality

/-!
# Conditional entropy grows when adjoining a variable (Nielsen & Chuang, Problem 11.3, part 1)

For a tripartite distribution `p : ι × κ × μ → ℝ` of `(X, Y, Z)` (read as `ι × (κ × μ)`), this file
states the classical **conditional-entropy monotonicity** of Nielsen & Chuang, Problem 11.3,
part 1.

## Main results

* `Real.condEntropyPairGivenLast` — the pair conditional entropy `H(X, Y | Z) = H(X, Y, Z) − H(Z)`.
* `Real.condEntropy_marginalFstLast_le_condEntropyPairGivenLast` — Nielsen & Chuang, Problem 11.3,
  part 1: `H(X | Z) ≤ H(X, Y | Z)`.
-/

@[expose] public section

namespace Real

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- **The pair conditional entropy** `H(X, Y | Z) = H(X, Y, Z) − H(Z)` of a tripartite distribution
`p : ι × κ × μ → ℝ`. -/
noncomputable def condEntropyPairGivenLast (p : ι × κ × μ → ℝ) : ℝ :=
  entropy p - entropy (marginalSnd (marginalSnd p))

/-- **Nielsen & Chuang, Problem 11.3, part 1**: conditioning on `Z`, adjoining a variable `Y` to the
un-conditioned side never decreases the conditional entropy — `H(X | Z) ≤ H(X, Y | Z)`. Here
`H(X | Z) = condEntropy (marginalFstLast p)` is the conditional entropy of the `(X,
Z)`-marginal. -/
theorem condEntropy_marginalFstLast_le_condEntropyPairGivenLast {p : ι × κ × μ → ℝ}
    (hp : ∀ q, 0 ≤ p q) :
    condEntropy (marginalFstLast p) ≤ condEntropyPairGivenLast p := sorry

end Real
