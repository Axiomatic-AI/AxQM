/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.ConditionalEntropy

/-!
# Mutual information of random variables, and a superadditivity counterexample

For a finite sample space `Ω` with a discrete distribution `p : Ω → ℝ` and two *random variables*
`f : Ω → β`, `g : Ω → γ` into finite types, the **mutual information** of `f` and `g` is
`H(f : g) = H(f) + H(g) − H(f, g)`.

## Main declarations

* `Real.mutualInfoMap` — `H(f : g)`, the mutual information of two random variables.
* `Real.exists_mutualInfo_not_superadditive_counterexample` and
  `Real.not_forall_mutualInfo_superadditive` — the mutual information is **not** always
  superadditive (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
  Exercise 11.9).
-/

@[expose] public section

namespace Real

variable {Ω β γ : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **mutual information** `H(f : g) = H(f) + H(g) − H(f, g)` of two random variables
`f : Ω → β`, `g : Ω → γ` on a common finite sample space with distribution `p : Ω → ℝ`, defined
through the laws of `f`, `g`, and the tuple `(f, g)` (all via `Real.entropyMap`). -/
noncomputable def mutualInfoMap (p : Ω → ℝ) (f : Ω → β) (g : Ω → γ) : ℝ :=
  entropyMap p f + entropyMap p g - entropyMap p (fun ω => (f ω, g ω))

/-- **Explicit counterexample to superadditivity of the mutual information** (Nielsen & Chuang,
*Quantum Computation and Quantum Information*, Exercise 11.9).

There exist a finite probability space and random variables `X₁, X₂, Y₁, Y₂` realising the
copied-variable configuration `X₂ ≡ Y₁ ≡ Y₂ ≡ X₁` of the exercise, for which

`H(X₁ : Y₁) + H(X₂ : Y₂) > H(X₁, X₂ : Y₁, Y₂)`,

so the inequality `H(X₁ : Y₁) + H(X₂ : Y₂) ≤ H(X₁, X₂ : Y₁, Y₂)` — superadditivity of the mutual
information (N&C eq. (11.35)) — does **not** hold. -/
theorem exists_mutualInfo_not_superadditive_counterexample :
    ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω) (p : Ω → ℝ) (X₁ X₂ Y₁ Y₂ : Ω → Fin 2),
      (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω = 1) ∧ X₂ = X₁ ∧ Y₁ = X₁ ∧ Y₂ = X₁ ∧
      mutualInfoMap p X₁ Y₁ + mutualInfoMap p X₂ Y₂ >
        mutualInfoMap p (fun ω => (X₁ ω, X₂ ω)) (fun ω => (Y₁ ω, Y₂ ω)) := sorry

/-- **Superadditivity of the mutual information is not a theorem** (Nielsen & Chuang, Exercise
11.9): it is *not* the case that for all finite random variables `X₁, X₂, Y₁, Y₂` on a finite
probability space,
`H(X₁ : Y₁) + H(X₂ : Y₂) ≤ H(X₁, X₂ : Y₁, Y₂)`. -/
theorem not_forall_mutualInfo_superadditive :
    ¬ ∀ (Ω αX₁ αX₂ αY₁ αY₂ : Type) [Fintype Ω] [DecidableEq Ω]
        [Fintype αX₁] [DecidableEq αX₁] [Fintype αX₂] [DecidableEq αX₂]
        [Fintype αY₁] [DecidableEq αY₁] [Fintype αY₂] [DecidableEq αY₂]
        (p : Ω → ℝ) (X₁ : Ω → αX₁) (X₂ : Ω → αX₂) (Y₁ : Ω → αY₁) (Y₂ : Ω → αY₂),
        (∀ ω, 0 ≤ p ω) → ∑ ω, p ω = 1 →
        mutualInfoMap p X₁ Y₁ + mutualInfoMap p X₂ Y₂ ≤
          mutualInfoMap p (fun ω => (X₁ ω, X₂ ω)) (fun ω => (Y₁ ω, Y₂ ω)) := sorry

end Real
