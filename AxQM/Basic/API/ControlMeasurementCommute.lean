/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.CompositeMeasurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM — measuring the control commutes with a controlled gate

The computational-basis measurement of the control qubit, the classically-controlled gate family,
and the operator commutation between them that N&C's Exercise 4.35 turns on.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The projective **measurement of the control qubit** in the computational basis, on `qubit ⊗ S`.
This is the measurement N&C's Exercise 4.35 performs on the control wire. -/
def controlMeasurement (S : QSystem) : Measurement (Fin 2) (qubit ⊗ S) :=
  (Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin 2) ℂ)).onLeft S

/-- The operators of `controlMeasurement` are the computational-basis control projectors
`Mᵢ = |i⟩⟨i| ⊗ 1` on `qubit ⊗ S`. -/
theorem controlMeasurement_op (S : QSystem) (i : Fin 2) :
    (controlMeasurement S).op i
      = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec)
          (1 : S.space →L[ℂ] S.space) := by
  rw [controlMeasurement, Measurement.onLeft_op, Measurement.ofOrthonormalBasis_op]
  -- `basisFun i = single i 1 = (qubitBasis i).vec`; matched up to the
  -- `qubit.space`/`EuclideanSpace` FunLike-instance defeq (which `rw`/`simp` key on but
  -- `exact` tolerates) via `congrArg`.
  exact congrArg
    (fun v => TensorProduct.mapL (InnerProductSpace.rankOne ℂ v v) (1 : S.space →L[ℂ] S.space))
    ((EuclideanSpace.basisFun_apply (Fin 2) ℂ i).trans (qubitBasis_vec i).symm)

/-- The **classically-controlled gate** applied on the branch of measurement outcome `i`: the
identity for `i = 0` and `1 ⊗ U` (`Evolution.onRight U qubit`, i.e. `U` on the target) for `i = 1`.
This is the gate `Uᶜᵒⁿᵗʳᵒˡ` conditioned on the measured control bit in the rightmost circuit of
N&C Exercise 4.35. -/
def classicalControl (U : Evolution S) : Fin 2 → Evolution (qubit ⊗ S) :=
  ![Evolution.id, Evolution.onRight U qubit]

@[simp]
theorem classicalControl_zero (U : Evolution S) : classicalControl U 0 = Evolution.id := rfl

@[simp]
theorem classicalControl_one (U : Evolution S) :
    classicalControl U 1 = Evolution.onRight U qubit := rfl

/-- **The commutation of Exercise 4.35** `Mᵢ · C(U) = Wᵢ · Mᵢ`: composing the control-projector `Mᵢ
= |i⟩⟨i| ⊗ 1` after the controlled-`U` gate equals the classical-control gate `Wᵢ` after `Mᵢ`. -/
theorem controlMeasurement_op_comp_controlledUnitary (U : Evolution S) (i : Fin 2) :
    ((controlMeasurement S).op i).comp (controlledUnitary U).op
      = (classicalControl U i).op.comp ((controlMeasurement S).op i) := by
  fin_cases i
  · simp only [Fin.mk_zero, Fin.isValue]
    rw [controlMeasurement_op, controlledUnitary_op, classicalControl_zero, Evolution.id_op]
    change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
          (1 : S.space →L[ℂ] S.space)).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
          + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
              U.op)
      = (1 : qubit.space ⊗[ℂ] S.space →L[ℂ] qubit.space ⊗[ℂ] S.space).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1)
    rw [ContinuousLinearMap.comp_add, TensorProduct.mapL_comp, TensorProduct.mapL_comp,
      rankOne_qubitBasis_comp_self 0, rankOne_qubitBasis_comp_orthogonal (by decide),
      TensorProduct.mapL_zero_left, add_zero]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [controlMeasurement_op, controlledUnitary_op, classicalControl_one]
    change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
          (1 : S.space →L[ℂ] S.space)).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
          + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
              U.op)
      = (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) U.op).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) 1)
    rw [ContinuousLinearMap.comp_add, TensorProduct.mapL_comp, TensorProduct.mapL_comp,
      rankOne_qubitBasis_comp_orthogonal (by decide), rankOne_qubitBasis_comp_self 1,
      TensorProduct.mapL_zero_left, zero_add, TensorProduct.mapL_comp]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]

end AxQM
