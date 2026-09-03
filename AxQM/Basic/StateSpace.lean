/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.QSystem
import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# AxQM — state space and states

The primitive for the *state* of a quantum system.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- A quantum **state** of the system `S` is a density
operator: a positive operator of trace one. Subsumes pure and mixed states alike. -/
@[ext]
structure State (S : QSystem) where
  /-- The underlying density operator. -/
  op : S →L[ℂ] S
  /-- The operator is a density operator: positive with trace one. -/
  isDensity : op.IsDensityOp

/-- A **pure state** of the system `S` is a unit
vector, determined up to a global phase. -/
@[ext]
structure PureState (S : QSystem) where
  /-- The underlying unit vector. -/
  vec : S
  /-- The vector is normalized: `‖vec‖ = 1`. -/
  normalized : ‖vec‖ = 1

variable {S : QSystem}

namespace State

/-- A state has trace one. -/
theorem trace_op_eq_one (ρ : State S) :
    LinearMap.trace ℂ S (ρ.op : S →ₗ[ℂ] S) = 1 :=
  ρ.isDensity.trace_eq_one

/-- A state's operator is positive. -/
theorem isPositive_op (ρ : State S) : ρ.op.IsPositive := ρ.isDensity.isPositive

/-- **A state's operator is nonzero.** -/
theorem op_ne_zero (ρ : State S) : (ρ.op : S →ₗ[ℂ] S) ≠ 0 := fun h ↦ by
  have := ρ.trace_op_eq_one
  rw [h, map_zero] at this
  exact one_ne_zero this.symm

/-- **A state forces a nontrivial space**: the existence of a `State S` implies
`Nontrivial S.space`. -/
theorem nontrivial_space (ρ : State S) : Nontrivial S.space :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦
    absurd ρ.trace_op_eq_one (by simp [Subsingleton.elim (ρ.op : S →ₗ[ℂ] S) 0])

end State

namespace PureState

/-- The state `|ψ⟩⟨ψ|` of a pure state `ψ` — the rank-one projector. -/
def toState (ψ : PureState S) : State S where
  op := InnerProductSpace.rankOne ℂ ψ.vec ψ.vec
  isDensity := ContinuousLinearMap.isDensityOp_rankOne_self ψ.normalized

@[simp]
theorem toState_op (ψ : PureState S) :
    ψ.toState.op = InnerProductSpace.rankOne ℂ ψ.vec ψ.vec := rfl

/-- A pure state coerces to its density-operator state `|ψ⟩⟨ψ|`. -/
instance : Coe (PureState S) (State S) := ⟨toState⟩

end PureState

end AxQM
