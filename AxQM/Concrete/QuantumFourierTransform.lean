/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Concrete: the `d`-dimensional quantum Fourier transform matrix and its unitarity

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §5.1 (eq. 5.2) defines the
**quantum Fourier transform** on an orthonormal basis `|0⟩, …, |d-1⟩` by its action on basis
states.

## Main declarations
* `qftPrimitiveRoot d = e^{2πi/d}` — the primitive `d`-th root of unity generating the transform.
* `qftMatrix d` — the matrix `Fₖⱼ = (1/√d) · ω^{jk}` (`ω = qftPrimitiveRoot d`).
* `qftMatrix_apply` — the entry in the literal `(1/√d) · e^{2πi jk/d}` form of (5.2).
* `qftMatrix_star_mul_self` — `F† F = 1`.
* `qftMatrix_mem_unitaryGroup` — `F ∈ Matrix.unitaryGroup (Fin d) ℂ`.
-/

namespace AxQM.Concrete

open Complex
open scoped Matrix

/-- The **primitive `d`-th root of unity** `ω = e^{2πi/d}` generating the `d`-dimensional quantum
Fourier transform. -/
noncomputable def qftPrimitiveRoot (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

/-- The **`d`-dimensional quantum Fourier transform matrix** (Nielsen & Chuang eq. 5.2), with
`(k, j)` entry `Fₖⱼ = (1/√d) · ω^{jk}` for `ω = qftPrimitiveRoot d`. Column `j` is the image of the
basis vector `|j⟩` under the transform. -/
noncomputable def qftMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun k j => (Real.sqrt d : ℂ)⁻¹ * qftPrimitiveRoot d ^ ((j : ℕ) * (k : ℕ))

/-- The quantum Fourier transform entry in the **literal exponential form** of Nielsen & Chuang eq.
(5.2): `Fₖⱼ = (1/√d) · e^{2πi jk/d}`. -/
theorem qftMatrix_apply (d : ℕ) (k j : Fin d) :
    qftMatrix d k j
      = (Real.sqrt d : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d) := by
  rw [qftMatrix, qftPrimitiveRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **Conjugate-transpose entry of the quantum Fourier transform matrix:** `(Fᴴ)ⱼₖ = (1/√d) ·
e^{−2πi jk/d}`, the inverse-DFT amplitude. -/
theorem qftMatrix_conjTranspose_apply (d : ℕ) (j k : Fin d) :
    (qftMatrix d)ᴴ j k
      = (Real.sqrt d : ℂ)⁻¹
        * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)) := by
  rw [Matrix.conjTranspose_apply, qftMatrix_apply, ← starRingEnd_apply, map_mul]
  congr 1
  · rw [map_inv₀, Complex.conj_ofReal]
  · rw [← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
    ring

/-- The generating root of unity is closed under conjugation with `conj ω = ω⁻¹`. -/
theorem qftPrimitiveRoot_conj (d : ℕ) :
    (starRingEnd ℂ) (qftPrimitiveRoot d) = (qftPrimitiveRoot d)⁻¹ := by
  rw [qftPrimitiveRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_natCast]
  ring

/-- Conjugation of the generating root, in `star` form. -/
theorem qftPrimitiveRoot_star (d : ℕ) :
    star (qftPrimitiveRoot d) = (qftPrimitiveRoot d)⁻¹ := by
  rw [← starRingEnd_apply]; exact qftPrimitiveRoot_conj d

/-- **The quantum Fourier transform matrix is an isometry:** `F† F = 1`. -/
theorem qftMatrix_star_mul_self (d : ℕ) [NeZero d] :
    star (qftMatrix d) * qftMatrix d = 1 := by
  have hd : (d : ℕ) ≠ 0 := NeZero.ne d
  have hω : IsPrimitiveRoot (qftPrimitiveRoot d) d := Complex.isPrimitiveRoot_exp d hd
  have hω0 : qftPrimitiveRoot d ≠ 0 := by rw [qftPrimitiveRoot]; exact Complex.exp_ne_zero _
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin d,
      (star (qftMatrix d)) i k * qftMatrix d k j
        = (Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹
          * ((qftPrimitiveRoot d ^ (i : ℕ))⁻¹ * qftPrimitiveRoot d ^ (j : ℕ)) ^ (k : ℕ) := by
    intro k
    rw [Matrix.star_apply]
    simp only [qftMatrix, star_mul', star_pow, star_inv₀, qftPrimitiveRoot_star,
      Complex.star_def, Complex.conj_ofReal, mul_pow, inv_pow, ← pow_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ((qftPrimitiveRoot d ^ (i : ℕ))⁻¹ * qftPrimitiveRoot d ^ (j : ℕ)) ^ k) d]
  set ζ : ℂ := (qftPrimitiveRoot d ^ (i : ℕ))⁻¹ * qftPrimitiveRoot d ^ (j : ℕ) with hζ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hsq : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
  by_cases hij : i = j
  · subst hij
    have hz1 : ζ = 1 := by rw [hζ]; exact inv_mul_cancel₀ (pow_ne_zero _ hω0)
    rw [hz1, if_pos rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← mul_inv, hsq, inv_mul_cancel₀ hd0]
  · have hζ1 : ζ ≠ 1 := by
      rw [hζ]
      intro h
      rw [inv_mul_eq_one₀ (pow_ne_zero _ hω0)] at h
      exact hij (Fin.ext (hω.pow_inj i.isLt j.isLt h))
    have hζd : ζ ^ d = 1 := by
      rw [hζ, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ) d, mul_comm (j : ℕ) d,
        pow_mul, pow_mul]
      simp [hω.pow_eq_one]
    rw [geom_sum_eq hζ1 d, hζd, sub_self, zero_div, mul_zero, if_neg hij]

/-- **The quantum Fourier transform matrix is unitary:** `F ∈ Matrix.unitaryGroup (Fin d) ℂ`
(Nielsen & Chuang, Exercise 5.1 / the unitarity underlying Problem 5.1). -/
theorem qftMatrix_mem_unitaryGroup (d : ℕ) [NeZero d] :
    qftMatrix d ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (qftMatrix_star_mul_self d)

end AxQM.Concrete
