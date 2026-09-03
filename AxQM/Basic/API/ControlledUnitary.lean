/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.BellReducedState
import AxQM.Concrete.Pauli
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the controlled-`U` gate and CNOT

The operator-level form of Nielsen & Chuang's controlled operations (N&C §4.3): the
single-qubit-controlled unitary `C(U)` and, as its canonical instance, the controlled-`NOT`
gate.

## Main declarations
* `pauliXGate` — the Pauli-`X` (quantum `NOT`) gate as an `Evolution qubit`, built from
  `Concrete.pauliX` through `Matrix.toEuclideanCLM`; unitarity is transported from
  `Concrete.pauliX_mem_unitaryGroup` (N&C Exercise 2.19).
* `controlledUnitary U` — the **controlled-`U` operation** `C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`
  on `qubit ⊗ S` (control qubit on the left, target system `S` arbitrary), N&C eq. (4.24). This is
  a genuine `Evolution`: the unitarity obligation is exactly the statement that the
  block-diagonal operator is unitary, discharged in `controlledUnitary_op_mem_unitary`.
* `cnotGate = controlledUnitary pauliXGate` — the **controlled-`NOT`** gate on `qubit ⊗ qubit`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **Pauli-`X` gate** `X` (the quantum `NOT`) as a closed-system `Evolution` of the qubit. -/
def pauliXGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.pauliX_mem_unitaryGroup

/-- The underlying operator of `pauliXGate` is `Matrix.toEuclideanCLM Concrete.pauliX`. -/
@[simp]
theorem pauliXGate_op :
    pauliXGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX := rfl

/-- The computational-basis rank-one projectors are **idempotent**: `|i⟩⟨i| · |i⟩⟨i| = |i⟩⟨i|`
(from `⟨i|i⟩ = 1`). Shared building block for the block-diagonal algebra of `controlledUnitary`. -/
theorem rankOne_qubitBasis_comp_self (i : Fin 2) :
    (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec).comp
        (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec)
      = InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec := by
  rw [InnerProductSpace.rankOne_comp_rankOne, qubitBasis_inner_qubitBasis]; simp

/-- The computational-basis rank-one projectors are **orthogonal**: `|i⟩⟨i| · |j⟩⟨j| = 0` for
`i ≠ j` (from `⟨i|j⟩ = 0`). Shared building block for the block-diagonal algebra of
`controlledUnitary`. -/
theorem rankOne_qubitBasis_comp_orthogonal {i j : Fin 2} (hij : i ≠ j) :
    (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec).comp
        (InnerProductSpace.rankOne ℂ (qubitBasis j).vec (qubitBasis j).vec) = 0 := by
  rw [InnerProductSpace.rankOne_comp_rankOne, qubitBasis_inner_qubitBasis]; simp [hij]

/-- The identity operator composed with itself is the identity, `1 ∘ 1 = 1` (the `Evolution`-target
`I·I = I` step in the controlled-`U` block algebra). -/
theorem one_comp_one : (1 : S.space →L[ℂ] S.space).comp (1 : S.space →L[ℂ] S.space) = 1 := by
  rw [← ContinuousLinearMap.mul_def, mul_one]

/-- **The controlled-`U` operator is unitary** (N&C §4.3). For a single-qubit-controlled unitary,
the block-diagonal operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` on `qubit.space ⊗ S.space` lies in the
unitary group: `C(U)† C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U†U = I` (the cross terms drop by
orthogonality `⟨0|1⟩ = 0`, and `|0⟩⟨0| + |1⟩⟨1| = I`), and symmetrically `C(U) C(U)† = I`.
-/
theorem controlledUnitary_op_mem_unitary (U : Evolution S) :
    (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) U.op)
      ∈ unitary (qubit.space ⊗[ℂ] S.space →L[ℂ] qubit.space ⊗[ℂ] S.space) := by
  set p0 := InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec with hp0
  set p1 := InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec with hp1
  -- rank-one projector composition: `|i⟩⟨i| |j⟩⟨j| = δ_{ij} |i⟩⟨i|` (shared projector lemmas)
  have h00 : p0.comp p0 = p0 := by rw [hp0]; exact rankOne_qubitBasis_comp_self 0
  have h11 : p1.comp p1 = p1 := by rw [hp1]; exact rankOne_qubitBasis_comp_self 1
  have h01 : p0.comp p1 = 0 := by
    rw [hp0, hp1]; exact rankOne_qubitBasis_comp_orthogonal (by decide)
  have h10 : p1.comp p0 = 0 := by
    rw [hp0, hp1]; exact rankOne_qubitBasis_comp_orthogonal (by decide)
  -- the projectors are self-adjoint and resolve the identity
  have hadj0 : adjoint p0 = p0 := by rw [hp0, InnerProductSpace.adjoint_rankOne]
  have hadj1 : adjoint p1 = p1 := by rw [hp1, InnerProductSpace.adjoint_rankOne]
  have hadjone : adjoint (1 : S.space →L[ℂ] S.space) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hsum : p0 + p1 = 1 := by
    rw [hp0, hp1]; have := sum_rankOne_qubitBasis_eq_one; rwa [Fin.sum_univ_two] at this
  -- unitarity of the target gate `U`
  have hUU : (adjoint U.op).comp U.op = 1 := U.adjoint_comp_self
  have hUUr : U.op.comp (adjoint U.op) = 1 := U.comp_adjoint_self
  have hadjop : adjoint (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL p1 U.op)
      = TensorProduct.mapL p0 1 + TensorProduct.mapL p1 (adjoint U.op) := by
    simp only [map_add, TensorProduct.mapL_adjoint, hadj0, hadj1, hadjone]
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def, hadjop,
      comp_add, add_comp, add_comp, TensorProduct.mapL_comp, TensorProduct.mapL_comp,
      TensorProduct.mapL_comp, TensorProduct.mapL_comp, h00, h01, h10, h11, hUU, one_comp_one,
      TensorProduct.mapL_zero_left, TensorProduct.mapL_zero_left, add_zero, zero_add,
      ← TensorProduct.mapL_add_left, hsum, TensorProduct.mapL_one]
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def, hadjop,
      comp_add, add_comp, add_comp, TensorProduct.mapL_comp, TensorProduct.mapL_comp,
      TensorProduct.mapL_comp, TensorProduct.mapL_comp, h00, h01, h10, h11, hUUr, one_comp_one,
      TensorProduct.mapL_zero_left, TensorProduct.mapL_zero_left, add_zero, zero_add,
      ← TensorProduct.mapL_add_left, hsum, TensorProduct.mapL_one]

/-- **The controlled-`U` gate** `C(U)` (Nielsen & Chuang §4.3, eq. 4.24): the `Evolution` on the
composite `qubit ⊗ S` whose operator is `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` — the identity on the target when
the control qubit is `|0⟩`, and the unitary `U` on the target when it is `|1⟩`. Unitarity (the
`Evolution` obligation) is `controlledUnitary_op_mem_unitary`. -/
def controlledUnitary (U : Evolution S) : Evolution (qubit ⊗ S) where
  op := TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
      (1 : S.space →L[ℂ] S.space)
    + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) U.op
  unitary := controlledUnitary_op_mem_unitary U

/-- The underlying operator of `controlledUnitary U` is `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`. -/
@[simp]
theorem controlledUnitary_op (U : Evolution S) :
    (controlledUnitary U).op
      = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
        + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
            U.op := rfl

/-- **The controlled-`NOT` (CNOT) gate** on two qubits (Nielsen & Chuang §1.3.2), the controlled-`U`
gate with `U = X`: it flips the target qubit exactly when the control qubit is `|1⟩`. -/
def cnotGate : Evolution (qubit ⊗ qubit) := controlledUnitary pauliXGate

end AxQM
