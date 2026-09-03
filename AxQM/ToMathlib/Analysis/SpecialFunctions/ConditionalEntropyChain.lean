/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# Chaining rule for conditional entropies (Nielsen & Chuang, Theorem 11.4)

The **chaining rule for conditional entropies**, eq. (11.27).

## Main results

* `Real.condEntropy_law_chain` — the chaining rule (11.27) for a sequence of random variables.
-/

@[expose] public section

namespace Real

variable {Ω : Type*} [Fintype Ω]

/-- The **law** (push-forward distribution) `law μ X x = ∑_{ω : X ω = x} μ ω` of a random variable
`X : Ω → γ` under the weight `μ : Ω → ℝ`. When `μ` is a probability weight this is the probability
mass function of `X`; the definition makes sense for any real weight. -/
noncomputable def law {γ : Type*} [DecidableEq γ] (μ : Ω → ℝ) (X : Ω → γ) : γ → ℝ :=
  fun x ↦ ∑ ω, if X ω = x then μ ω else 0

/-- **Chaining rule for conditional entropies** (Nielsen & Chuang, Theorem 11.4, eq. (11.27)): for
random variables `X₀, X₁, …` (a sequence, of which only the first `n` enter) and `Y` on a finite
sample space `Ω` with weight `μ`, valued in common finite alphabets,
`H(X₀, …, X_{n-1} | Y) = ∑ᵢ H(Xᵢ | Y, X₀, …, Xᵢ₋₁)`. The identity holds for any weight `μ`, with no
normalisation needed. -/
theorem condEntropy_law_chain {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : Ω → ℝ) (X : ℕ → Ω → α) (Y : Ω → β) (n : ℕ) :
    condEntropy (law μ fun ω ↦ (fun i : Fin n ↦ X i ω, Y ω))
      = ∑ i : Fin n,
          condEntropy (law μ fun ω ↦ (X i ω, (Y ω, fun j : Fin (i : ℕ) ↦ X j ω))) := sorry

end Real
