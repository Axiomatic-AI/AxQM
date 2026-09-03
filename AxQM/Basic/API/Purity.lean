/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PureState
import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# AxQM.Basic.API — purity of a state

The **purity** `tr(ρ²)` of a state and the predicate that a state is pure (N&C Exercise 2.71, the
criterion for deciding whether a state is mixed or pure).
-/

noncomputable section

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The **purity** `tr(ρ²)` of a state `ρ`, as a real number. Since `ρ` is a positive operator, `ρ²
= ρ.op * ρ.op` is positive and its trace is real; `purity` records that real trace. -/
def State.purity (ρ : State S) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S ((ρ.op * ρ.op : S →L[ℂ] S) : S →ₗ[ℂ] S))

/-- A state `ρ` **is pure** when it is the rank-one projector `|ψ⟩⟨ψ|` of some pure state `ψ`, i.e.
`ρ = ψ.toState`. -/
def State.IsPure (ρ : State S) : Prop :=
  ∃ ψ : PureState S, ρ = ψ.toState

end AxQM
