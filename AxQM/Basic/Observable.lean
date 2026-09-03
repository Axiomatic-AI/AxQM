/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# AxQM — observables

A measurable quantity: an **observable** is a bundled
self-adjoint operator on a system `S`. By the spectral theorem it has an orthonormal
eigenbasis with real eigenvalues — its possible measurement values.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- An **observable** on the system `S` is a
self-adjoint operator; its real spectrum is the set of possible measurement values. -/
structure Observable (S : QSystem) where
  /-- The underlying operator. -/
  op : S →L[ℂ] S
  /-- The operator is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint op

variable {S : QSystem}

namespace PureState

/-- The **expectation value** `⟪A⟫_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the pure
state `ψ`. Real because `A` is self-adjoint. -/
def expectation (ψ : PureState S) (A : Observable S) : ℝ := (⟪ψ.vec, A.op ψ.vec⟫_ℂ).re

end PureState

namespace State

/-- The **expectation value** `⟪A⟫_ρ = Tr(ρ A)` of an observable `A` in the state
`ρ`. Real because `ρ`, `A` are self-adjoint. -/
def expectation (ρ : State S) (A : Observable S) : ℝ :=
  (LinearMap.trace ℂ S ((ρ.op ∘L A.op : S →L[ℂ] S) : S →ₗ[ℂ] S)).re

end State

end AxQM
