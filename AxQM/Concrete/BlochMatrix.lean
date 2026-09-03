/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Analysis.Matrix.PosDef

/-!
# Concrete: the Bloch matrix `ρ = (I + r·σ)/2`

The `2 × 2` complex matrix `½ (I + r·σ)` of a real three-vector `r`.
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped ComplexOrder

/-- The **Bloch matrix** `½ (I + r·σ)` for a real three-vector `r`: the `2 × 2` complex matrix
representing a single-qubit density matrix with Bloch vector `r` (Nielsen & Chuang, Exercise
2.72, eq. 2.175). Built from the identity and the Pauli combination `Concrete.pauliDot r`. -/
noncomputable def blochMatrix (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + pauliDot r)

/-- `blochMatrix r` as a single explicit `2 × 2` matrix
`½ !![1 + r₂, r₀ − i r₁; r₀ + i r₁, 1 − r₂]`. -/
theorem blochMatrix_eq (r : Fin 3 → ℝ) :
    blochMatrix r =
      !![(2⁻¹ : ℂ) * (1 + (r 2 : ℂ)), (2⁻¹ : ℂ) * ((r 0 : ℂ) - (r 1 : ℂ) * I);
         (2⁻¹ : ℂ) * ((r 0 : ℂ) + (r 1 : ℂ) * I), (2⁻¹ : ℂ) * (1 - (r 2 : ℂ))] := by
  rw [blochMatrix, pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, mul_add, sub_eq_add_neg]

/-- **`tr (blochMatrix r) = 1`**: the trace of the Bloch matrix is one — the trace-one half of the
statement that `blochMatrix r` is a density matrix. -/
theorem blochMatrix_trace (r : Fin 3 → ℝ) : (blochMatrix r).trace = 1 := by
  rw [blochMatrix_eq, Matrix.trace_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

/-- **`det (blochMatrix r) = (1 − ‖r‖²)/4`** (with `‖r‖² = r₀² + r₁² + r₂²`). -/
theorem blochMatrix_det (r : Fin 3 → ℝ) :
    (blochMatrix r).det = ((1 - (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 4 : ℝ) := by
  rw [blochMatrix_eq, Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow, Complex.I_re,
      Complex.I_im] <;>
    ring

/-- **Positivity criterion for the Bloch matrix (Nielsen & Chuang, Exercise 2.72(1), positivity
half).** `blochMatrix r` is positive semidefinite iff `‖r‖² = r₀² + r₁² + r₂² ≤ 1` —
equivalently `‖r‖ ≤ 1`, since `‖r‖ ≥ 0`.
-/
theorem blochMatrix_posSemidef_iff (r : Fin 3 → ℝ) :
    (blochMatrix r).PosSemidef ↔ r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1 := by
  constructor
  · -- Forward: positive semidefinite ⇒ nonnegative determinant ⇒ ‖r‖² ≤ 1.
    intro h
    have hdet := h.det_nonneg
    rw [blochMatrix_det, Complex.zero_le_real] at hdet
    linarith
  · -- Reverse: the Gram + scaled-identity decomposition.
    intro hr
    have hAh : (1 + pauliDot r)ᴴ = 1 + pauliDot r := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, pauliDot_conjTranspose]
    -- (I+A)ᴴ(I+A) = I + 2A + A² = I + 2A + ‖r‖²·I.
    have hgram : (1 + pauliDot r)ᴴ * (1 + pauliDot r)
        = 1 + pauliDot r + pauliDot r
          + ((r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hAh,
        show (1 + pauliDot r) * (1 + pauliDot r)
            = 1 + pauliDot r + pauliDot r + pauliDot r * pauliDot r from by noncomm_ring,
        pauliDot_mul_self]
    -- The scalar-level identity blochMatrix r = ¼(I+A)ᴴ(I+A) + ¼(1-‖r‖²)·I. The two coefficients
    -- are written as coerced reals so the nonnegativity goals reduce via `Complex.zero_le_real`.
    have heq : blochMatrix r
        = (((4⁻¹ : ℝ) : ℂ)) • ((1 + pauliDot r)ᴴ * (1 + pauliDot r))
          + (((1 - (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 4 : ℝ) : ℂ)
            • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hgram, blochMatrix, pauliDot_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul] <;>
        push_cast <;> ring
    rw [heq]
    refine (Matrix.posSemidef_conjTranspose_mul_self _).smul ?_ |>.add
      (Matrix.PosSemidef.one.smul ?_)
    · rw [Complex.zero_le_real]; norm_num
    · rw [Complex.zero_le_real]; linarith

end AxQM.Concrete
