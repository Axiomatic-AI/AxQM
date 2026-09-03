/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.QSystem
import AxQM.Basic.StateSpace
import AxQM.Basic.Observable
import AxQM.Basic.Measurement
import AxQM.Basic.Evolution

/-!
# AxQM — system isomorphisms (`S ≃ₛ T`)

A **system isomorphism** `S ≃ₛ T` is an inner-product isometry of the underlying operators,
`S.space ≃ₗᵢ[ℂ] T.space`. This file also defines the **transport** of a `State`, a `PureState`,
an `Evolution` and a `Measurement` along such an isomorphism.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- A **system isomorphism**: an inner-product isometry between the underlying operators of two
systems: the identification along which primitives are transported between systems the physicist
regards as the same up to reorganization. -/
structure QSystem.Iso (S T : QSystem) where
  /-- The underlying operator isometry. -/
  toIsometry : S.space ≃ₗᵢ[ℂ] T.space

@[inherit_doc] scoped infix:25 " ≃ₛ " => QSystem.Iso

namespace QSystem.Iso

variable {S T U : QSystem}

instance : CoeFun (S ≃ₛ T) (fun _ ↦ S.space → T.space) := ⟨fun e ↦ e.toIsometry⟩

/-- The identity system isomorphism. -/
def refl (S : QSystem) : S ≃ₛ S := ⟨LinearIsometryEquiv.refl ℂ S.space⟩

/-- The inverse system isomorphism. -/
def symm (e : S ≃ₛ T) : T ≃ₛ S := ⟨e.toIsometry.symm⟩

/-- Composition of system isomorphisms. -/
def trans (e : S ≃ₛ T) (f : T ≃ₛ U) : S ≃ₛ U := ⟨e.toIsometry.trans f.toIsometry⟩

end QSystem.Iso

variable {S T : QSystem}

/-- **Transport a state** along a system isomorphism: `ρ ↦ e ρ e⁻¹`. -/
def State.congr (e : S ≃ₛ T) (ρ : State S) : State T where
  op := e.toIsometry.conjStarAlgEquiv ρ.op
  isDensity := e.toIsometry.conjStarAlgEquiv_isDensityOp_iff.mpr ρ.isDensity

/-- **Transport a pure state** along a system isomorphism: `ψ ↦ e ψ`. Norm-preserving. -/
def PureState.congr (e : S ≃ₛ T) (ψ : PureState S) : PureState T where
  vec := e.toIsometry ψ.vec
  normalized := by rw [LinearIsometryEquiv.norm_map, ψ.normalized]

/-- **Transport an evolution** along a system isomorphism. -/
def Evolution.congr (e : S ≃ₛ T) (U : Evolution S) : Evolution T where
  op := e.toIsometry.conjStarAlgEquiv U.op
  unitary := by
    have hU := Unitary.mem_iff.mp U.unitary
    rw [Unitary.mem_iff]
    refine ⟨?_, ?_⟩
    · rw [← map_star, ← map_mul, hU.1, map_one]
    · rw [← map_star, ← map_mul, hU.2, map_one]

/-- **Transport a measurement** along a system isomorphism. -/
def Measurement.congr {ι : Type*} [Fintype ι] (e : S ≃ₛ T) (m : Measurement ι S) :
    Measurement ι T where
  op i := e.toIsometry.conjStarAlgEquiv (m.op i)
  complete := by
    have step : ∀ i, (adjoint (e.toIsometry.conjStarAlgEquiv (m.op i))).comp
        (e.toIsometry.conjStarAlgEquiv (m.op i))
        = e.toIsometry.conjStarAlgEquiv ((adjoint (m.op i)).comp (m.op i)) := by
      intro i
      have hstar : adjoint (e.toIsometry.conjStarAlgEquiv (m.op i))
          = e.toIsometry.conjStarAlgEquiv (adjoint (m.op i)) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
          ContinuousLinearMap.star_eq_adjoint]
      rw [hstar, ← ContinuousLinearMap.mul_def, ← map_mul, ContinuousLinearMap.mul_def]
    simp_rw [step]
    rw [← map_sum, m.complete, map_one]

end AxQM
