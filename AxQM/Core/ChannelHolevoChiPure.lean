/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChi
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy

/-!
# The channel Holevo χ quantity is achieved by pure-state ensembles

Nielsen & Chuang, Exercise 12.11 (p. 555), asks to show that the maximum defining the Holevo χ
quantity of a channel `E` (eq. (12.71), the left-hand side of the HSW theorem) is achieved by
pure-state ensembles.

## Main definitions and results

* `AxQM.channelHolevoChiPureSet` — the χ-value set over pure-state input ensembles.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The set of Holevo χ values `χ({pⱼ, E(ψⱼ)})` of the *output* ensemble obtained by pushing a
finite **pure-state** input ensemble `{pⱼ, |ψⱼ⟩}` (indexed by `Fin n`, WLOG for finite ensembles)
through `E`. Its supremum is the pure-restricted channel Holevo χ. -/
def channelHolevoChiPureSet (E : State S → State S) : Set ℝ :=
  {x | ∃ (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
      (ψ : Fin n → PureState S), x = State.holevoChi p hp hsum (fun i => E (ψ i).toState)}

end AxQM
