/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.LinearAlgebra.Matrix.HermitianUnitary
import Mathlib.Data.Complex.Basic

/-!
# Concrete: the Pauli matrices and the combination `n · σ`

The three `2 × 2` Pauli matrices `X`, `Y`, `Z` over `ℂ` and, for a real three-vector `n`, the
Hermitian combination `n · σ = n₀ X + n₁ Y + n₂ Z`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The Pauli `X` matrix `!![0, 1; 1, 0]`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix `!![0, -i; i, 0]`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The Pauli `Z` matrix `!![1, 0; 0, -1]`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The combination `n · σ = n₀ • X + n₁ • Y + n₂ • Z` for a real three-vector `n`. This is
Nielsen & Chuang's `n̂ · σ ≡ Σᵢ nᵢ σᵢ`. -/
def pauliDot (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (n 0 : ℂ) • pauliX + (n 1 : ℂ) • pauliY + (n 2 : ℂ) • pauliZ

/-- `n · σ` as a single explicit `2 × 2` matrix. -/
theorem pauliDot_eq (n : Fin 3 → ℝ) :
    pauliDot n =
      !![(n 2 : ℂ), (n 0 : ℂ) - (n 1 : ℂ) * I;
         (n 0 : ℂ) + (n 1 : ℂ) * I, -(n 2 : ℂ)] := by
  simp only [pauliDot, pauliX, pauliY, pauliZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]

/-- `pauliDot` is additive in its vector argument. -/
theorem pauliDot_add (u w : Fin 3 → ℝ) : pauliDot (u + w) = pauliDot u + pauliDot w := by
  simp only [pauliDot, Pi.add_apply, Complex.ofReal_add]
  module

/-- `pauliDot` is ℝ-homogeneous in its vector argument (as a `ℂ`-scalar multiple). -/
theorem pauliDot_smul (a : ℝ) (u : Fin 3 → ℝ) :
    pauliDot (a • u) = (a : ℂ) • pauliDot u := by
  simp only [pauliDot, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  module

/-- `pauliDot` subtracts. -/
theorem pauliDot_sub (u w : Fin 3 → ℝ) : pauliDot (u - w) = pauliDot u - pauliDot w := by
  simp only [pauliDot, Pi.sub_apply, Complex.ofReal_sub]
  module

/-- `pauliDot` negates. -/
theorem pauliDot_neg (u : Fin 3 → ℝ) : pauliDot (-u) = -pauliDot u := by
  simp only [pauliDot, Pi.neg_apply, Complex.ofReal_neg]
  module

/-- `n · σ` equals its own conjugate transpose. -/
theorem pauliDot_conjTranspose (n : Fin 3 → ℝ) : (pauliDot n)ᴴ = pauliDot n := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Complex.ext_iff]

/-- `n · σ` is Hermitian, for any real three-vector `n` (Nielsen & Chuang, Exercise 2.19). -/
theorem pauliDot_isHermitian (n : Fin 3 → ℝ) : (pauliDot n).IsHermitian :=
  pauliDot_conjTranspose n

/-- `(n · σ)² = ‖n‖² • I`, where `‖n‖² = n₀² + n₁² + n₂²`. -/
theorem pauliDot_mul_self (n : Fin 3 → ℝ) :
    pauliDot n * pauliDot n =
      (((n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    push_cast <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring

/-- For a unit vector `n` (`n₀² + n₁² + n₂² = 1`), `(n · σ)² = I`. -/
theorem pauliDot_mul_self_of_unit {n : Fin 3 → ℝ}
    (h : (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 = 1) :
    pauliDot n * pauliDot n = 1 := by
  rw [pauliDot_mul_self, h]; simp

/-- Pauli `X` is an involution: `X² = I`. -/
theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `Y` is an involution: `Y² = I`. -/
theorem pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `Z` is an involution: `Z² = I`. -/
theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `X` is Hermitian (`Xᴴ = X`). -/
theorem pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

/-- Pauli `Y` is Hermitian (`Yᴴ = Y`). -/
theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.conjTranspose_apply]

/-- Pauli `Z` is Hermitian (`Zᴴ = Z`). -/
theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]

/-- Pauli `X` is unitary (`Xᴴ X = I`, i.e. `X ∈ unitaryGroup`). -/
theorem pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliX_isHermitian.mem_unitaryGroup pauliX_mul_self

/-- Pauli `Y` is unitary (`Yᴴ Y = I`, i.e. `Y ∈ unitaryGroup`). -/
theorem pauliY_mem_unitaryGroup : pauliY ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliY_isHermitian.mem_unitaryGroup pauliY_mul_self

/-- Pauli `Z` is unitary (`Zᴴ Z = I`, i.e. `Z ∈ unitaryGroup`). -/
theorem pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliZ_isHermitian.mem_unitaryGroup pauliZ_mul_self

/-- Pauli `X` is traceless: `tr X = 0`. -/
theorem pauliX_trace : pauliX.trace = 0 := sorry

/-- Pauli `Y` is traceless: `tr Y = 0`. -/
theorem pauliY_trace : pauliY.trace = 0 := sorry

/-- Pauli `Z` is traceless: `tr Z = 0`. -/
theorem pauliZ_trace : pauliZ.trace = 0 := by
  simp [pauliZ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- The Pauli matrices indexed by `Fin 4` in Nielsen & Chuang's convention: `σ₀ = I`, `σ₁ = X`,
`σ₂ = Y`, `σ₃ = Z`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pauliX, pauliY, pauliZ]

/-- Every Pauli matrix is an involution (Nielsen & Chuang, eq. 2.76): `σᵢ² = I` for
`i = 0, 1, 2, 3`. -/
theorem pauli_mul_self (i : Fin 4) : pauli i * pauli i = 1 := by
  fin_cases i <;>
    simp [pauli, pauliX_mul_self, pauliY_mul_self, pauliZ_mul_self]

/-- The anticommutation relations in indexed form (Nielsen & Chuang, eq. 2.75): for distinct
non-identity indices `i, j` — i.e. `i ≠ j`, both in `{1, 2, 3}`, expressed as `i, j ≠ 0` since
`0` is the sole excluded index of `Fin 4` — the anticommutator vanishes, `σᵢ σⱼ + σⱼ σᵢ = 0`.
The identity `σ₀ = I` is excluded because `{I, σ} = 2σ ≠ 0`, and the equal-index diagonal because
`{σ, σ} = 2σ² = 2I ≠ 0`. -/
theorem pauli_anticomm {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    pauli i * pauli j + pauli j * pauli i = 0 := sorry

/-- Each indexed Pauli matrix is Hermitian: `σᵢᴴ = σᵢ` for `i = 0, 1, 2, 3`. -/
theorem pauli_isHermitian (m : Fin 4) : (pauli m).IsHermitian := by
  fin_cases m
  · exact Matrix.isHermitian_one
  · exact pauliX_isHermitian
  · exact pauliY_isHermitian
  · exact pauliZ_isHermitian

/-- Entrywise Hermiticity of a Pauli matrix. -/
theorem pauli_conj_apply (m : Fin 4) (a b : Fin 2) : star (pauli m a b) = pauli m b a := by
  have h := congrFun (congrFun (pauli_isHermitian m) b) a
  rwa [Matrix.conjTranspose_apply] at h

/-- **Single-qubit trace orthogonality** (the `d = 2` case of Nielsen & Chuang, Exercise 2.39):
`tr(σᵢ σⱼ) = 2 δᵢⱼ`. -/
theorem pauli_trace_mul (i j : Fin 4) :
    (pauli i * pauli j).trace = if i = j then (2 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliX, pauliY, pauliZ, Matrix.trace_fin_two, Complex.ext_iff] <;> norm_num

end AxQM.Concrete
