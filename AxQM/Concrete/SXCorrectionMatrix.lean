/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGateCircuit
import AxQM.Concrete.Pauli

/-!
# Concrete: the observable `M = e^{-iπ/4}SX` and its transversal correction `ZSX`

Nielsen & Chuang **Exercise 10.71** ("Fault-tolerant measurement of `M = e^{-iπ/4}SX`", §10.6.3,
p. 491) asks to *verify* that the fault-tolerant measurement procedure of Fig. 10.28 — specialised
to the observable `M = e^{-iπ/4}SX` by the "slight modification" of p. 491 — is a correct method for
measuring `M`. This file proves the `2 × 2` complex-matrix **algebra** the verification rests
on.
-/

open Matrix Complex

noncomputable section

namespace AxQM.Concrete

/-- The single-qubit observable `M = e^{-iπ/4}·SX` of Nielsen & Chuang Exercise 10.71, with
`SX = Concrete.sxMatrix = !![0,1;i,0]`. It is the observable whose fault-tolerant measurement
creates the ancilla for the π/8 gate. -/
def mMatrix : Matrix (Fin 2) (Fin 2) ℂ := Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix

/-- `M = !![0, (1−i)/√2; (1+i)/√2, 0]` as an explicit matrix. -/
theorem mMatrix_eq :
    mMatrix = !![0, invSqrt2 - invSqrt2 * Complex.I; invSqrt2 + invSqrt2 * Complex.I, 0] := by
  have h2 := Complex.I_mul_I
  rw [mMatrix, exp_neg_pi_div_four_mul_I_ofReal, sxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  all_goals linear_combination (-invSqrt2) * h2

/-- **`M` is Hermitian**: `M† = M`. -/
theorem mMatrix_conjTranspose : mMatrixᴴ = mMatrix := by
  rw [mMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, invSqrt2, Complex.ext_iff]

/-- **`M` is an involution**: `M² = 1`, so `M` has eigenvalues `±1`. -/
theorem mMatrix_mul_self : mMatrix * mMatrix = 1 := by
  have h1 := invSqrt2_mul_self
  have h2 := Complex.I_mul_I
  rw [mMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (1 - Complex.I * Complex.I) * h1 - (2⁻¹ : ℂ) * h2

/-- **`M` is unitary** (`M ∈ U(2)`). -/
theorem mMatrix_mem_unitaryGroup : mMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [Matrix.star_eq_conjTranspose, mMatrix_conjTranspose]; exact mMatrix_mul_self)

/-- The `-1` eigenvector `|Θ⁻⟩ = (|0⟩ − e^{iπ/4}|1⟩)/√2` of `M`, as a column vector
`Fin 2 → ℂ`. -/
def thetaMinusVec : Fin 2 → ℂ := ![invSqrt2, -(invSqrt2 * tMatrix 1 1)]

/-- **The nontrivial diagonal entry of `T` has unit modulus**. -/
theorem norm_tMatrix_one_one : ‖tMatrix 1 1‖ = 1 := by
  have h : ‖tMatrix 1 1‖ * ‖tMatrix 1 1‖ = 1 := by
    rw [← norm_mul, tMatrix_apply_one_one_mul_self, Complex.norm_I]
  nlinarith [norm_nonneg (tMatrix 1 1), h]

/-- The **transversal correction gate `ZSX = Z·S·X`** used per qubit in the Exercise 10.71
procedure, defined as `pauliZ · sxMatrix` (with `sxMatrix = S·X`). -/
def zsxMatrix : Matrix (Fin 2) (Fin 2) ℂ := pauliZ * sxMatrix

/-- `ZSX = !![0,1;−i,0]` as an explicit matrix. -/
theorem zsxMatrix_eq : zsxMatrix = !![0, 1; -Complex.I, 0] := by
  rw [zsxMatrix, sxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`ZSX` is unitary** (`ZSX ∈ U(2)`). Unlike `M`, `ZSX` is *not* self-adjoint
(`(ZSX)† = !![0,i;1,0] ≠ ZSX`); it is the per-qubit *correction gate* applied by the transversal
controlled-`ZSX`, not an observable. -/
theorem zsxMatrix_mem_unitaryGroup : zsxMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, zsxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

end AxQM.Concrete
