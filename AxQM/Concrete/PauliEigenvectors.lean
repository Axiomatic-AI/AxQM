/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliOuterProduct
import Mathlib.Analysis.Complex.Norm

/-!
# Concrete: eigendecomposition of the Pauli matrices (Nielsen & Chuang, Exercise 2.11)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.11
("Eigendecomposition of the Pauli matrices", p. 69) asks to find the **eigenvectors**,
**eigenvalues**, and **diagonal representations** of the Pauli matrices `X`, `Y`, `Z`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The normalization constant `1/√2`, as a complex number. It is the shared coefficient of
the `X`- and `Y`-eigenvectors `|±⟩`, `|±i⟩`. -/
noncomputable def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- `(1/√2)·(1/√2) = 1/2`. -/
theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = 2⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `‖(1/√2 : ℂ)‖² = 1/2`: the squared magnitude of the shared amplitude of `|±⟩`. -/
theorem norm_invSqrt2_sq : ‖(invSqrt2 : ℂ)‖ ^ 2 = 2⁻¹ := by
  rw [invSqrt2, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)), inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `1/√2` is real, hence fixed by complex conjugation: `conj (1/√2) = 1/√2`. -/
theorem invSqrt2_star : star invSqrt2 = invSqrt2 := by simp [invSqrt2]

/-- The self outer product `|v⟩⟨v|` of a column vector `v : Fin 2 → ℂ`, as the `2 × 2`
matrix `vecMulVec v (star v)` with `(a, b)` entry `vₐ · conj v_b` (the bra `⟨v|` is the
conjugate of the ket `|v⟩`). When `v` is a unit vector this is the rank-one orthogonal
projector onto `v`; a diagonal representation is a signed sum of such projectors. -/
def outerSelf (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec v (star v)

/-- `|0⟩` is an eigenvector of `Z` with eigenvalue `+1`: `Z|0⟩ = |0⟩`. -/
theorem pauliZ_mulVec_ket_zero : pauliZ *ᵥ ket 0 = (1 : ℂ) • ket 0 := by
  ext i; fin_cases i <;> simp [pauliZ, ket, Matrix.mulVec]

/-- `|1⟩` is an eigenvector of `Z` with eigenvalue `-1`: `Z|1⟩ = -|1⟩`. -/
theorem pauliZ_mulVec_ket_one : pauliZ *ᵥ ket 1 = (-1 : ℂ) • ket 1 := by
  ext i; fin_cases i <;> simp [pauliZ, ket, Matrix.mulVec]

/-- The diagonal representation of `Z`: `Z = |0⟩⟨0| - |1⟩⟨1|`. -/
theorem pauliZ_eq_outerSelf_sub : pauliZ = outerSelf (ket 0) - outerSelf (ket 1) := sorry

/-- The `X`-eigenvector `|+⟩ = (|0⟩ + |1⟩)/√2 = (1/√2, 1/√2)`, eigenvalue `+1`. -/
noncomputable def xPlus : Fin 2 → ℂ := ![invSqrt2, invSqrt2]

/-- The `X`-eigenvector `|-⟩ = (|0⟩ - |1⟩)/√2 = (1/√2, -1/√2)`, eigenvalue `-1`. -/
noncomputable def xMinus : Fin 2 → ℂ := ![invSqrt2, -invSqrt2]

/-- Both components of `|+⟩ = (1/√2, 1/√2)` equal `1/√2`. -/
@[simp] theorem xPlus_apply (i : Fin 2) : xPlus i = invSqrt2 := by fin_cases i <;> rfl

/-- `|+⟩` is an eigenvector of `X` with eigenvalue `+1`: `X|+⟩ = |+⟩`. -/
theorem pauliX_mulVec_xPlus : pauliX *ᵥ xPlus = (1 : ℂ) • xPlus := sorry

/-- `|-⟩` is an eigenvector of `X` with eigenvalue `-1`: `X|-⟩ = -|-⟩`. -/
theorem pauliX_mulVec_xMinus : pauliX *ᵥ xMinus = (-1 : ℂ) • xMinus := sorry

/-- The diagonal representation of `X`: `X = |+⟩⟨+| - |-⟩⟨-|`. -/
theorem pauliX_eq_outerSelf_sub : pauliX = outerSelf xPlus - outerSelf xMinus := sorry

/-- The `Y`-eigenvector `|+i⟩ = (|0⟩ + i|1⟩)/√2 = (1/√2, i/√2)`, eigenvalue `+1`. -/
noncomputable def yPlus : Fin 2 → ℂ := ![invSqrt2, invSqrt2 * I]

/-- The `Y`-eigenvector `|-i⟩ = (|0⟩ - i|1⟩)/√2 = (1/√2, -i/√2)`, eigenvalue `-1`. -/
noncomputable def yMinus : Fin 2 → ℂ := ![invSqrt2, -(invSqrt2 * I)]

/-- `|+i⟩` is an eigenvector of `Y` with eigenvalue `+1`: `Y|+i⟩ = |+i⟩`. -/
theorem pauliY_mulVec_yPlus : pauliY *ᵥ yPlus = (1 : ℂ) • yPlus := sorry

/-- `|-i⟩` is an eigenvector of `Y` with eigenvalue `-1`: `Y|-i⟩ = -|-i⟩`. -/
theorem pauliY_mulVec_yMinus : pauliY *ᵥ yMinus = (-1 : ℂ) • yMinus := sorry

/-- The diagonal representation of `Y`: `Y = |+i⟩⟨+i| - |-i⟩⟨-i|`. -/
theorem pauliY_eq_outerSelf_sub : pauliY = outerSelf yPlus - outerSelf yMinus := sorry

end AxQM.Concrete
