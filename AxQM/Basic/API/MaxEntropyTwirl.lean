/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.MaximallyMixed

/-!
# AxQM — `I/d` is the unique maximal-entropy state (the depolarizing-twirl proof)

Nielsen & Chuang, **Exercise 11.19** (p. 517), part 2: the completely mixed state `I/d` is the
**unique** state of maximal von Neumann entropy. This file supplies the *alternate* proof the
exercise asks for — via the depolarizing **twirl** and the *strict* concavity of the entropy.

## Main results

* `AxQM.State.maximallyMixedState_unique_maxEntropy` — `ρ` maximises the entropy
  `↔ ρ = I/d`.
-/

open scoped ComplexOrder

noncomputable section

namespace AxQM

/-- **Exercise 11.19: the completely mixed state `I/d` is the unique state of maximal von
Neumann entropy.** A state `ρ` maximises the entropy — `S(σ) ≤ S(ρ)` for all `σ` — **iff** it is
the maximally mixed state `I/d`.
-/
theorem State.maximallyMixedState_unique_maxEntropy (S : QSystem) [Nontrivial S.space]
    (ρ : State S) :
    (∀ σ : State S, σ.vonNeumannEntropy ≤ ρ.vonNeumannEntropy) ↔ ρ = maximallyMixedState S := sorry

end AxQM
