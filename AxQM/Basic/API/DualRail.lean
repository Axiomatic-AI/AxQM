/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitaryDecomposition

/-!
# AxQM.Basic.API — the dual-rail single-photon qubit

The **dual-rail representation** of a logical qubit into two optical modes
(Nielsen & Chuang §7.4.2): a single photon shared between two modes.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The dual-rail **logical zero** `|0_L⟩ = |01⟩`, the product pure state `|0⟩ ⊗ |1⟩` of
`qubit ⊗ qubit`: a single photon in the second mode. -/
def dualRailZero : PureState (qubit ⊗ qubit) := qubitBasis 0 ⊗ qubitBasis 1

/-- The dual-rail **logical one** `|1_L⟩ = |10⟩`, the product pure state `|1⟩ ⊗ |0⟩` of
`qubit ⊗ qubit`: a single photon in the first mode. -/
def dualRailOne : PureState (qubit ⊗ qubit) := qubitBasis 1 ⊗ qubitBasis 0

@[simp]
theorem dualRailZero_vec : dualRailZero.vec = (qubitBasis 0 ⊗ qubitBasis 1).vec := rfl

@[simp]
theorem dualRailOne_vec : dualRailOne.vec = (qubitBasis 1 ⊗ qubitBasis 0).vec := rfl

/-- **Orthogonality of the dual-rail codewords:** `⟨01|10⟩ = 0`. -/
theorem dualRailZero_inner_dualRailOne :
    (inner ℂ dualRailZero.vec dualRailOne.vec : ℂ) = 0 := by
  rw [dualRailZero_vec, dualRailOne_vec, qubitBasis_tmul_inner]
  norm_num

/-- The **dual-rail superposition vector** `c₀·|01⟩ + c₁·|10⟩` in the two-qubit state space
`qubit.space ⊗[ℂ] qubit.space`. -/
def dualRailVec (c0 c1 : ℂ) : (qubit ⊗ qubit).space :=
  c0 • dualRailZero.vec + c1 • dualRailOne.vec

/-- **The dual-rail superposition is normalised** when its amplitudes are:
`‖c₀·|01⟩ + c₁·|10⟩‖ = 1` given `‖c₀‖² + ‖c₁‖² = 1`. -/
theorem norm_dualRailVec (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖dualRailVec c0 c1‖ = 1 := by
  have hsq : ‖dualRailVec c0 c1‖ ^ 2 = 1 := by
    rw [dualRailVec, norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, dualRailZero.normalized,
      dualRailOne.normalized, inner_smul_left, inner_smul_right, dualRailZero_inner_dualRailOne]
    simp only [mul_one, mul_zero, map_zero, add_zero]
    linarith [h]
  nlinarith [norm_nonneg (dualRailVec c0 c1), hsq]

/-- The **dual-rail logical state** `c₀|01⟩ + c₁|10⟩` as a `PureState (qubit ⊗ qubit)`, for
amplitudes with `‖c₀‖² + ‖c₁‖² = 1`. The general single-photon qubit encoded in two optical modes
(Nielsen & Chuang §7.4.2); the optical gates of §7.4.2 are the unitaries acting on it. -/
def dualRail (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) : PureState (qubit ⊗ qubit) where
  vec := dualRailVec c0 c1
  normalized := norm_dualRailVec c0 c1 h

/-- **A phase shifter on the second mode acts by `[1, e^{iα}]` on that mode's occupation:** `(1 ⊗
P(α))|a b⟩ = [1, e^{iα}]_b · |a b⟩`. The phase shifter `(phaseShiftGate α).onRight qubit` leaves
the first factor alone and applies `P(α) = diag(1, e^{iα})` to the second, so the two-mode basis
state `|a⟩ ⊗ |b⟩` picks up `1` when `b = 0` (no photon in that mode) and `e^{iα}` when `b = 1`. -/
theorem phaseShiftGate_onRight_op_qubitBasis (α : ℝ) (a b : Fin 2) :
    ((phaseShiftGate α).onRight qubit).op ((qubitBasis a ⊗ qubitBasis b).vec)
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] b • ((qubitBasis a ⊗ qubitBasis b).vec) := by
  rw [← Evolution.evolvePure_vec, Evolution.onRight_evolvePure]
  simp only [PureState.tmul_vec, Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
  exact TensorProduct.tmul_smul _ _ _

/-- **A phase shifter on the second mode multiplies the `|01⟩` amplitude by `e^{iα}`:**
`(1 ⊗ P(α))(c₀|01⟩ + c₁|10⟩) = e^{iα}c₀|01⟩ + c₁|10⟩`. Only the `|01⟩` codeword — whose photon
sits in the phase-shifted (second) mode — acquires the phase; the `|10⟩` codeword is untouched.
The operator form of the dual-rail phase gate `diag(e^{iα}, 1)` (Exercise 7.7's `diag(e^{iπ}, 1)`
at `α = π`). -/
theorem phaseShiftGate_onRight_op_dualRailVec (α : ℝ) (c0 c1 : ℂ) :
    ((phaseShiftGate α).onRight qubit).op (dualRailVec c0 c1)
      = dualRailVec (Complex.exp ((α : ℂ) * Complex.I) * c0) c1 := by
  rw [dualRailVec, dualRailVec, dualRailZero_vec, dualRailOne_vec, map_add, map_smul, map_smul,
    phaseShiftGate_onRight_op_qubitBasis, phaseShiftGate_onRight_op_qubitBasis]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, one_smul, smul_smul]
  rw [mul_comm c0]

end AxQM
