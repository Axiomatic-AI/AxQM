/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MinimalEnsemble
import Mathlib.Analysis.InnerProductSpace.Trace
import AxQM.Basic.API.PseudoInverse

/-!
# AxQM — the probability formula for a minimal ensemble (N&C Ex 2.73)

Nielsen & Chuang, Exercise 2.73, second part: *in any minimal ensemble `{pᵢ, |ψᵢ⟩}` for `ρ` the
weight of each state is*
`pᵢ = 1 / ⟨ψᵢ|ρ⁻¹|ψᵢ⟩`,
where `ρ⁻¹` is the pseudo-inverse (`State.pseudoInverse`). This file proves that identity and
packages the matrix element `⟨ψ|ρ⁻¹|ψ⟩` as a real-valued function
(`State.pseudoInverseExpectation`).

## Main definitions

* `AxQM.State.pseudoInverseExpectation` — the real matrix element `⟨ψ|ρ⁻¹|ψ⟩` of the
  pseudo-inverse, `re ⟪ψ, ρ⁻¹ ψ⟫`.
* `AxQM.PureState.MemSupport` — the predicate `|ψ⟩ ∈ support ρ`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The pseudo-inverse expectation `⟨ψ|ρ⁻¹|ψ⟩`**: the real matrix
element of the pseudo-inverse `ρ⁻¹` in the pure state `|ψ⟩`, `re ⟪ψ, ρ⁻¹ ψ⟫`. Real because `ρ⁻¹`
is self-adjoint. -/
def pseudoInverseExpectation (ρ : State S) (ψ : PureState S) : ℝ :=
  (inner ℂ ψ.vec (ρ.pseudoInverse ψ.vec)).re

end State

namespace PureState

/-- **A pure state lies in the support of `ρ`**: `|ψ⟩ ∈ support ρ`, i.e. the operator membership
`ψ.vec ∈ ρ.support`. -/
def MemSupport (ψ : PureState S) (ρ : State S) : Prop :=
  ψ.vec ∈ ρ.support

end PureState

end AxQM
