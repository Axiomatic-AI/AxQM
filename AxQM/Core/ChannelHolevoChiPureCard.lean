/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChiPure
import AxQM.Basic.API.EntropyMixLine
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The channel Holevo χ over pure-state ensembles of at most `d²` states

Nielsen & Chuang, Exercise 12.11 (p. 555) asks to show that the maximum defining the Holevo χ
quantity of a channel `E` (eq. (12.71), the left-hand side of the HSW theorem) is achieved by an
ensemble of at most `d²` **pure** states, where `d = dim` of the channel input.

## Main definitions

* `AxQM.channelHolevoChiPureLeCardSet` — the χ-value set over pure-state input ensembles of
  at most `d²` elements.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.3.2, Theorem 12.8, eq. (12.71); Exercise 12.11.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The set of Holevo χ values `χ({pⱼ, E(ψⱼ)})` of the *output* ensemble obtained by pushing a
finite **pure-state** input ensemble `{pⱼ, |ψⱼ⟩}` of at most `d² = S.dim ^ 2` states (indexed by
`Fin n` with `n ≤ S.dim ^ 2`) through `E`; `d` is the dimension of the channel input. -/
def channelHolevoChiPureLeCardSet (E : State S → State S) : Set ℝ :=
  {x | ∃ (n : ℕ) (_ : n ≤ S.dim ^ 2) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
      (ψ : Fin n → PureState S), x = State.holevoChi p hp hsum (fun i => E (ψ i).toState)}

end AxQM
