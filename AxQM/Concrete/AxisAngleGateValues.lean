/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import AxQM.Concrete.Hadamard
import AxQM.Concrete.Pauli
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: axis-angle parameters for the phase gate (Nielsen & Chuang, Ex. 4.8(3))

Part 3 of **Nielsen & Chuang, Exercise 4.8** asks for the explicit values of `α, θ, n̂` in the
axis-angle decomposition `U = e^{iα} R_n̂(θ)` (eq. 4.9) for the phase gate `S = diag(1, i)`. This
file proves the `2 × 2` matrix identity that pins those values.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **phase gate** `S = diag(1, i)` (Nielsen & Chuang, §4.2), the diagonal single-qubit gate
`!![1, 0; 0, i]`. -/
def sMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.I]

/-- **Nielsen & Chuang, Exercise 4.8(3) (phase gate as an axis rotation).** The phase gate equals
`R_z(π/2)` up to the global phase `e^{iπ/4}`: `S = e^{iπ/4} • R_z(π/2)` (so `α = π/4`, `θ =
π/2`, `n̂ = ẑ`). -/
theorem sMatrix_eq_expPiDivFour_smul_rotZ :
    sMatrix = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) • rotZ (Real.pi / 2) := by
  have hI : Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I := by
    exact_mod_cast Complex.exp_pi_div_two_mul_I
  rw [rotZ_eq]
  unfold sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.smul_apply,
      smul_eq_mul, neg_mul, mul_zero, Complex.ofReal_div, Complex.ofReal_ofNat]
  · -- (0,0): `1 = exp(iπ/4) · exp(-i(π/2)/2)`
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  · -- (1,1): `i = exp(iπ/4) · exp(i(π/2)/2)`, i.e. `exp(iπ/2) = i`
    rw [← Complex.exp_add,
      show (Real.pi : ℂ) / 4 * Complex.I + (Real.pi : ℂ) / 2 / 2 * Complex.I
          = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact hI.symm

/-- The phase gate `S = diag(1, i)` is unitary: it lies in the `2 × 2` unitary group. -/
theorem sMatrix_mem_unitaryGroup : sMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hc : Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) *
      star (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]; norm_num
  rw [sMatrix_eq_expPiDivFour_smul_rotZ, Matrix.mem_unitaryGroup_iff, star_smul,
    smul_mul_smul_comm, Matrix.mem_unitaryGroup_iff.mp (rotZ_mem_unitaryGroup _), hc, one_smul]

end AxQM.Concrete
