/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.Qudit
import AxQM.Concrete.ABCDecomposition

/-!
# AxQM.Basic.API — Figure 4.6: controlled-`U` from single-qubit gates and two CNOTs

Infrastructure for Nielsen & Chuang's **controlled-operation gate count** (N&C §4.3,
Figure 4.6): a single-qubit-controlled gate `C(U)` is built from *unconditional* single-qubit gates
and exactly **two** CNOTs, using the ABC decomposition of `U`. This is the
"one controlled-single-qubit gate costs two CNOTs" brick that the gate-counting of Exercise 4.22
(`C²(U)` from ≤ 8 one-qubit gates and 6 CNOTs) rests on, and it is reused by the other controlled-
gate constructions of Chapter 4 (Exercises 4.23, 4.28).

## Main declarations
* `phaseShiftGate α` — the **single-qubit phase-shift gate** `P(α) = diag(1, e^{iα})`, the general
  relative-phase gate (`S = P(π/2)`, `T = P(π/4)` are special cases), as an `Evolution qubit`.
  `phaseShiftGate_op`, `phaseShiftGate_op_apply_qubitBasis` (`P(α)|i⟩ = [1, e^{iα}]ᵢ |i⟩`) record
  its action.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap Matrix

noncomputable section

namespace AxQM

/-- **The phase-shift gate** `P(α) = diag(1, e^{iα})` as a closed-system `Evolution` of the qubit:
the operator diagonal in the computational basis with entries `1` on `|0⟩` and `e^{iα}` on `|1⟩`.
It is unitary because both entries have unit modulus. This is the general relative-phase gate
(N&C §4.2), with the `S` gate `P(π/2) = diag(1, i)` and the `T` gate `P(π/4) = diag(1, e^{iπ/4})` as
special cases; it is the phase gate placed on the control qubit in Figure 4.6's controlled-`U`
construction. -/
def phaseShiftGate (α : ℝ) : Evolution qubit where
  op := (EuclideanSpace.basisFun (Fin 2) ℂ).diagonalOperator
          (fun i => ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] i)
  unitary := by
    refine OrthonormalBasis.diagonalOperator_mem_unitary _ _ (fun i => ?_)
    fin_cases i <;> simp [Complex.norm_exp]

/-- The underlying operator of `phaseShiftGate α` is the computational-basis diagonal operator
with entries `[1, e^{iα}]`. -/
theorem phaseShiftGate_op (α : ℝ) :
    (phaseShiftGate α).op = (EuclideanSpace.basisFun (Fin 2) ℂ).diagonalOperator
      (fun i => ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] i) := rfl

/-- **Eigenvalue action of the phase-shift gate:** `P(α)|i⟩ = [1, e^{iα}]ᵢ |i⟩`, i.e. `P(α)` fixes
`|0⟩` and multiplies `|1⟩` by `e^{iα}`. -/
theorem phaseShiftGate_op_apply_qubitBasis (α : ℝ) (i : Fin 2) :
    (phaseShiftGate α).op (qubitBasis i).vec
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] i • (qubitBasis i).vec := by
  rw [qubitBasis_vec, phaseShiftGate_op]
  exact basisFun_diagonalOperator_apply_single _ i

end AxQM
