/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellBasis
import AxQM.Basic.API.MaximallyMixed
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite

/-!
# AxQM.Basic.API — the qubit resolution of identity

`∑ᵢ |i⟩⟨i| = I` for the computational basis of the qubit.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Resolution of identity for the qubit computational basis:** `∑ᵢ |i⟩⟨i| = I`. -/
theorem sum_rankOne_qubitBasis_eq_one :
    (∑ i : Fin 2, (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec :
      qubit.space →L[ℂ] qubit.space)) = 1 := by
  have h := OrthonormalBasis.sum_rankOne_eq_id (EuclideanSpace.basisFun (Fin 2) ℂ)
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [ContinuousLinearMap.one_def]; exact h

end AxQM
