/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# The data processing inequality (Nielsen & Chuang, Theorem 11.5)

For a tripartite distribution `p : ι × κ × μ → ℝ` of random variables `(X, Y, Z)`, this file proves
the **classical data processing inequality**: if `X → Y → Z` is a Markov chain, then
`H(X) ≥ H(X : Y) ≥ H(X : Z)`, where `H(X : Y)` is the mutual information. Intuitively, further
processing the output `Y` of a noisy channel cannot increase the information it carries about the
input `X`: once information is lost, it is gone forever.

## Main definitions and results

* `Real.marginalFstLast` — the `(X, Z)`-marginal `p_{XZ}(x, z) = ∑_y p(x, y, z)`.
* `Real.IsMarkovChain` — `X → Y → Z` is a Markov chain: `X` and `Z` are conditionally independent
  given `Y`, `p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)` (the division-free form of
  `p(z | x, y) = p(z | y)`, N&C eq. (11.36)). The condition is symmetric in `X` and `Z`, so it also
  expresses `Z → Y → X`.
* `Real.mutualInfo_marginalFstMid_le_marginalFst` — the first inequality `H(X : Y) ≤ H(X)` (needing
  no Markov hypothesis), and `Real.mutualInfo_marginalFstMid_eq_marginalFst_iff` its saturation
  condition: `H(X) = H(X : Y)` iff `X` is a deterministic function of `Y`, i.e. `X` is
  reconstructible from `Y`.
* `Real.mutualInfo_marginalFstLast_le_marginalFstMid` — the data processing inequality proper,
  `H(X : Z) ≤ H(X : Y)`, for a Markov chain.
-/

@[expose] public section

namespace Real

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- The joint `(X, Z)`-marginal `p_{XZ}(x, z) = ∑_y p(x, y, z)` of a tripartite distribution,
obtained by summing out the middle variable `Y`. -/
noncomputable def marginalFstLast (p : ι × κ × μ → ℝ) : ι × μ → ℝ := fun q ↦ ∑ y, p (q.1, y, q.2)

/-- **First inequality of the data processing inequality** (N&C Theorem 11.5): the mutual
information never exceeds the source entropy, `H(X : Y) ≤ H(X)`; this needs no Markov
hypothesis. -/
theorem mutualInfo_marginalFstMid_le_marginalFst {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    mutualInfo (marginalFstMid p) ≤ entropy (marginalFst p) := sorry

/-- **Saturation of the first inequality** (N&C Theorem 11.5, the "moreover"): `H(X) = H(X : Y)` if
and only if `X` is a deterministic function of `Y` — i.e. given `Y` one can reconstruct `X`. The
right-hand side `SndDeterminedByFst (fun w ↦ p_{XY}(w.2, w.1))` reads on the `(Y, X)`-marginal
as `∃ f, ∀ y x, p_{XY}(x, y) ≠ 0 → x = f y`. -/
theorem mutualInfo_marginalFstMid_eq_marginalFst_iff {p : ι × κ × μ → ℝ} [Nonempty ι]
    (hp : ∀ q, 0 ≤ p q) :
    mutualInfo (marginalFstMid p) = entropy (marginalFst p) ↔
      SndDeterminedByFst (fun w : κ × ι ↦ marginalFstMid p (w.2, w.1)) := sorry

/-- **The data processing inequality** (N&C Theorem 11.5): for a Markov chain `X → Y → Z`, the
mutual information decreases along the chain, `H(X : Z) ≤ H(X : Y)`. -/
theorem mutualInfo_marginalFstLast_le_marginalFstMid {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) (hm : IsMarkovChain p) :
    mutualInfo (marginalFstLast p) ≤ mutualInfo (marginalFstMid p) := sorry

end Real
