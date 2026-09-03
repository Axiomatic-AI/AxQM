/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.ProjectiveMeasurement

/-!
# The reset measurement `{|0⟩⟨0|, |0⟩⟨1|}`

The generalized measurement on a qubit with operators `M₀ = |0⟩⟨0|` and `M₁ = |0⟩⟨1|`, which
satisfy the completeness relation `M₀† M₀ + M₁† M₁ = I`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The reset measurement `{M₀ = |0⟩⟨0|, M₁ = |0⟩⟨1|}`.** Uniformly `Mᵢ = |0⟩⟨i| = rankOne |0⟩
|i⟩`. `M₁ = |0⟩⟨1|` is not self-adjoint, so this is a genuine *generalized* measurement, not a
projective one. -/
def resetMeasurement : Measurement (Fin 2) qubit where
  op i := rankOne ℂ (qubitBasis 0).vec (qubitBasis i).vec
  complete := by
    set b : OrthonormalBasis (Fin 2) ℂ qubit.space := EuclideanSpace.basisFun (Fin 2) ℂ with hb
    have hbv : ∀ i, (qubitBasis i).vec = b i := fun i => by
      rw [qubitBasis_vec]; exact (EuclideanSpace.basisFun_apply (Fin 2) ℂ i).symm
    have h00 : (inner ℂ (b 0) (b 0) : ℂ) = 1 := by simp
    simp only [hbv, adjoint_rankOne, rankOne_comp_rankOne, h00, one_smul]
    rw [b.sum_rankOne_eq_id, ContinuousLinearMap.one_def]

end AxQM
