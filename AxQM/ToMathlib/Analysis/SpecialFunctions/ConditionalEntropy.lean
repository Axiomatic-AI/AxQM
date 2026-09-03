/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Conditional Shannon entropy of random variables, and a strong-subadditivity counterexample

For a finite sample space `Ω` with a discrete distribution `p : Ω → ℝ` and a *random variable*
`f : Ω → β` into a finite type, the **entropy of the law of `f`** is the Shannon entropy of the
pushed-forward distribution `b ↦ ∑_{ω : f ω = b} p ω`.

## Main declarations

* `Real.entropyMap` — `H(f)`, the Shannon entropy of the law of a random variable `f`.
* `Real.condEntropyMap` — `H(f | g) = H(f, g) − H(g)`.
* `Real.not_forall_conditional_strong_subadditivity` — the classical conditional-entropy inequality
  `H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)` can **fail** (Nielsen & Chuang, *Quantum
  Computation and Quantum Information*, Problem 11.4(2)).
-/

@[expose] public section

namespace Real

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

/-- The Shannon entropy (in nats) of the *law* of a random variable `f : Ω → β` under the
distribution `p : Ω → ℝ`: the entropy of the pushforward distribution
`b ↦ ∑_{ω : f ω = b} p ω`. Writing `H(f)` for this quantity, `entropyMap p f = H(f)`. -/
noncomputable def entropyMap (p : Ω → ℝ) (f : Ω → β) : ℝ :=
  entropy (fun b => ∑ ω, if f ω = b then p ω else 0)

/-- The **conditional Shannon entropy** of a random variable `f` given a random variable `g`,
`H(f | g) = H(f, g) − H(g)`, defined through the joint law of the tuple `(f, g)` and the law of
`g`. -/
noncomputable def condEntropyMap {γ : Type*} [Fintype γ] [DecidableEq γ]
    (p : Ω → ℝ) (f : Ω → β) (g : Ω → γ) : ℝ :=
  entropyMap p (fun ω => (f ω, g ω)) - entropyMap p g

/-- **The classical conditional form of strong subadditivity is not a theorem** (Nielsen &
Chuang, Problem 11.4(2)): it is *not* the case that for all finite random variables `A, B, C, D`
on a finite probability space,
`H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)`. -/
theorem not_forall_conditional_strong_subadditivity :
    ¬ ∀ (Ω αA αB αC αD : Type) [Fintype Ω] [DecidableEq Ω] [Fintype αA] [DecidableEq αA]
        [Fintype αB] [DecidableEq αB] [Fintype αC] [DecidableEq αC] [Fintype αD] [DecidableEq αD]
        (p : Ω → ℝ) (A : Ω → αA) (B : Ω → αB) (C : Ω → αC) (D : Ω → αD),
        (∀ ω, 0 ≤ p ω) → ∑ ω, p ω = 1 →
        condEntropyMap p D (fun ω => (A ω, B ω, C ω)) + condEntropyMap p D B ≤
          condEntropyMap p D (fun ω => (A ω, B ω)) + condEntropyMap p D (fun ω => (B ω, C ω)) :=
            sorry

end Real
