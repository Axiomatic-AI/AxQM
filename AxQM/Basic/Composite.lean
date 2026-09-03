/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.PartialTrace
import AxQM.Basic.Evolution
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM — composite systems

The state space of a composite system `S ⊗ T` is the **tensor product** of the
component state spaces (`QSystem.compose`). This file constructs joint states and evolutions
from component ones (N&C §2.2.8).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Composite pure state** `ψ ⊗ φ`: the product state of two pure states, on `S ⊗ T`. -/
def PureState.tmul (ψ : PureState S) (φ : PureState T) : PureState (S ⊗ T) where
  vec := ψ.vec ⊗ₜ[ℂ] φ.vec
  normalized := by
    have h : ‖(ψ.vec ⊗ₜ[ℂ] φ.vec : S.space ⊗[ℂ] T.space)‖ = 1 := by
      rw [TensorProduct.norm_tmul, ψ.normalized, φ.normalized, mul_one]
    exact h

@[inherit_doc] scoped infixr:70 " ⊗ " => PureState.tmul

@[simp]
theorem PureState.tmul_vec (ψ : PureState S) (φ : PureState T) :
    (ψ ⊗ φ).vec = ψ.vec ⊗ₜ[ℂ] φ.vec := rfl

/-- **Composite state** `ρ ⊗ σ`: the product of two states, on `S ⊗ T`. -/
def State.tmul (ρ : State S) (σ : State T) : State (S ⊗ T) where
  op := TensorProduct.mapL ρ.op σ.op
  isDensity := ContinuousLinearMap.IsDensityOp.mapL ρ.isDensity σ.isDensity

@[inherit_doc] scoped infixr:70 " ⊗ " => State.tmul

/-- **Composite evolution** `U ⊗ V`. -/
def Evolution.tmul (U : Evolution S) (V : Evolution T) : Evolution (S ⊗ T) where
  op := TensorProduct.mapL U.op V.op
  unitary := TensorProduct.mapL_mem_unitary U.unitary V.unitary

@[inherit_doc] scoped infixr:70 " ⊗ " => Evolution.tmul

/-- **A gate on the left factor**: `U ⊗ 1` acts as `U` on `S`, identity on `T`. -/
def Evolution.onLeft (U : Evolution S) (T : QSystem) : Evolution (S ⊗ T) := U ⊗ Evolution.id

/-- **A gate on the right factor**: `1 ⊗ V` acts as `V` on `T`, identity on `S`. -/
def Evolution.onRight (V : Evolution T) (S : QSystem) : Evolution (S ⊗ T) := Evolution.id ⊗ V

/-- **Canonical purification** of a state `ρ` (Nielsen–Chuang §2.5). -/
def State.purify (ρ : State S) :
    PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin S.dim))) where
  vec := TensorProduct.canonicalPurification ρ.isDensity (EuclideanSpace.basisFun _ ℂ)
  normalized := TensorProduct.norm_canonicalPurification ρ.isDensity _

end AxQM
