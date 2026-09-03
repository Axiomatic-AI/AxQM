/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.Basic.API.QuantumChannel

/-!
# The Holevo χ quantity of a quantum channel (N&C eq. (12.71))

The **Holevo χ quantity** of a trace-preserving quantum operation `E` is the left-hand side of the
Holevo–Schumacher–Westmoreland (HSW) theorem (Nielsen & Chuang, Theorem 12.8, eq. (12.71)).

## Main definitions and results

* `AxQM.channelHolevoChi` — the Holevo χ quantity `χ(E)` of a channel.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The set of Holevo χ values `χ({pⱼ, E(ρⱼ)})` of the *output* ensemble obtained by pushing a
finite input ensemble `{pⱼ, ρⱼ}` (indexed by `Fin n`, WLOG for finite ensembles) through `E`. Its
supremum is the channel Holevo χ quantity `channelHolevoChi E`. -/
def channelHolevoChiSet (E : State S → State S) : Set ℝ :=
  {x | ∃ (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : Fin n → State S),
      x = State.holevoChi p hp hsum (fun i => E (ρ i))}

/-- **The Holevo χ quantity of a quantum channel** `E` (Nielsen & Chuang, eq. (12.71)): the maximum
Holevo χ of the output ensemble `{pⱼ, E(ρⱼ)}` over all input ensembles `{pⱼ, ρⱼ}`,
`χ(E) = max_{{pⱼ,ρⱼ}} [S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ))]`. It is the left-hand side of the HSW
theorem `χ(E) = C⁽¹⁾(E)`. Realized as the supremum of `channelHolevoChiSet E`. -/
def channelHolevoChi (E : State S → State S) : ℝ :=
  sSup (channelHolevoChiSet E)

end AxQM
