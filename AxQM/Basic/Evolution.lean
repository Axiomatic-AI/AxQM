/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM — time evolution (closed systems)

An **evolution** of a system `S` is a unitary operator. It acts on states by conjugation
(`evolve`) and on pure states by application (`evolvePure`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- A closed-system **evolution** of the system `S` is a
unitary operator on its state space: `U† U = U U† = 1`. -/
@[ext]
structure Evolution (S : QSystem) where
  /-- The underlying unitary operator. -/
  op : S →L[ℂ] S
  /-- The operator is unitary. -/
  unitary : op ∈ unitary (S →L[ℂ] S)

variable {S : QSystem}

namespace Evolution

/-- The isometry identity `U† U = 1` extracted from unitarity. -/
theorem adjoint_comp_self (U : Evolution S) : (adjoint U.op).comp U.op = 1 := by
  have h := (Unitary.mem_iff.mp U.unitary).1
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] at h

/-- A unitary preserves norms: `‖U x‖ = ‖x‖`. -/
theorem norm_op_apply (U : Evolution S) (x : S) : ‖U.op x‖ = ‖x‖ := by
  have hxx : ⟪x, x⟫_ℂ = ⟪U.op x, U.op x⟫_ℂ := by
    calc ⟪x, x⟫_ℂ
        = ⟪x, ((adjoint U.op).comp U.op) x⟫_ℂ := by rw [U.adjoint_comp_self]; rfl
      _ = ⟪x, (adjoint U.op) (U.op x)⟫_ℂ := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪U.op x, U.op x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right U.op x (U.op x)
  have h2 : ‖U.op x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), ← hxx]
  rw [← Real.sqrt_sq (norm_nonneg (U.op x)), ← Real.sqrt_sq (norm_nonneg x), h2]

/-- **Evolution of a pure state** (Schrödinger picture): `ψ ↦ U ψ`. -/
def evolvePure (U : Evolution S) (ψ : PureState S) : PureState S where
  vec := U.op ψ.vec
  normalized := by rw [U.norm_op_apply, ψ.normalized]

@[simp]
theorem evolvePure_vec (U : Evolution S) (ψ : PureState S) :
    (U.evolvePure ψ).vec = U.op ψ.vec := rfl

/-- The **identity evolution**, the unit unitary `1`. -/
def id : Evolution S := ⟨1, one_mem _⟩

/-- The **composite evolution** `U ∘ V`, whose operator is `U.op ∘ V.op` (still
unitary, as the product of unitaries). -/
def comp (U V : Evolution S) : Evolution S :=
  ⟨U.op.comp V.op, mul_mem U.unitary V.unitary⟩

@[simp]
theorem id_op : (Evolution.id : Evolution S).op = 1 := rfl

@[simp]
theorem comp_op (U V : Evolution S) : (U.comp V).op = U.op.comp V.op := rfl

@[simp]
theorem comp_id (U : Evolution S) : U.comp Evolution.id = U := by
  ext1; rw [comp_op, id_op]; exact mul_one _

@[simp]
theorem id_comp (U : Evolution S) : Evolution.id.comp U = U := by
  ext1; rw [comp_op, id_op]; exact one_mul _

theorem comp_assoc (U V W : Evolution S) :
    (U.comp V).comp W = U.comp (V.comp W) := by
  ext1; simp only [comp_op, ContinuousLinearMap.comp_assoc]

/-- `Evolution S` is a monoid under composition `comp`, with unit the identity evolution `id`. -/
instance : Monoid (Evolution S) where
  mul := Evolution.comp
  one := Evolution.id
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

/-- **Evolution of a state**: `ρ ↦ U ρ U†`. -/
def evolve (U : Evolution S) (ρ : State S) : State S where
  op := U.op.comp (ρ.op.comp (adjoint U.op))
  isDensity := ContinuousLinearMap.IsDensityOp.conj_isometry U.adjoint_comp_self ρ.isDensity

@[simp]
theorem evolve_op (U : Evolution S) (ρ : State S) :
    (U.evolve ρ).op = U.op.comp (ρ.op.comp (adjoint U.op)) := rfl

end Evolution

end AxQM
