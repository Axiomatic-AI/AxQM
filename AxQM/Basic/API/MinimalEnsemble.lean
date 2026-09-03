/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.Support
import Mathlib.Analysis.InnerProductSpace.Positive
import AxQM.Basic.API.UnitaryFreedom

/-!
# AxQM — minimal ensembles for a density operator

Nielsen & Chuang, Exercise 2.73, single out the **minimal ensembles** of a density operator `ρ`:
an ensemble `{pᵢ, |ψᵢ⟩}` for `ρ` is *minimal* when its number of elements equals the **rank** of
`ρ`. This is the smallest an ensemble generating `ρ` can be, and the exercise studies which
support vectors can appear in a minimal ensemble, and with what probability.

## Main definitions

* `AxQM.Ensemble.IsMinimalFor` — the predicate `e.IsMinimalFor ρ`: the ensemble `e`
  generates `ρ` (`e.toState = ρ`) and has exactly `ρ.rank` elements (`e.card = ρ.rank`).
-/

open scoped InnerProductSpace
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- **A minimal ensemble for `ρ`**: an ensemble `e` that generates
`ρ` (`e.toState = ρ`) and has exactly `ρ.rank` elements (`e.card = ρ.rank`) — the fewest an ensemble
generating `ρ` can have. A predicate on the existing `Ensemble` primitive tying it to a specific
`ρ`, so existence/uniqueness statements quantify faithfully over `∀ e, e.IsMinimalFor ρ → …`. -/
def IsMinimalFor (e : Ensemble S) (ρ : State S) : Prop :=
  e.toState = ρ ∧ e.card = ρ.rank

end Ensemble

end AxQM
