/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import AxQM.Concrete.BlochMatrix
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Concrete: the rotation `R_n̂(θ)` rotates the Bloch vector

Nielsen & Chuang, Exercise 4.6 ("Bloch sphere interpretation of rotations") asks to show that the
qubit rotation `R_n̂(θ) = exp(−iθ n̂·σ/2)` (eq. 4.8) acts on a state with Bloch vector `⃗λ` by
rotating `⃗λ` through the angle `θ` about the `n̂` axis. This file develops the pure `2 × 2`
complex-matrix core of that fact: a statement about the conjugation `ρ ↦ R_n̂(θ) ρ R_n̂(θ)ᴴ`
acting on Bloch matrices.

## The 3D rotation and the conjugation identity

* `rot3D n θ` — the **3D rotation** of a vector about the unit axis `n` by angle `θ`, in Rodrigues
  form `R(θ)v = cos θ · v + sin θ · (n × v) + (1 − cos θ)(n·v) · n`. This is the map the qubit
  rotation induces on Bloch vectors.
* `pauliDot_conj_rotAxis` — the **conjugation identity** and heart of the exercise: for a unit axis
  `n`, `R_n̂(θ) · (v·σ) · R_n̂(θ)ᴴ = (R(θ)v)·σ`. Conjugating the Pauli combination `v·σ` by the
  spin-½ rotation is the Pauli combination of the *rotated* vector.
* `rot3D_sq_sum` — a rotation **preserves the squared length** of the Bloch vector. This keeps
  `rot3D n θ v` in the Bloch ball.

## Supporting Pauli identities

* `pauliDot_mul` — the **Pauli product rule** (vector form): `(a·σ)(b·σ) = (a·b) I + i (a×b)·σ`, the
  vector-calculus form of the multiplication table `σⱼσₖ = δⱼₖ I + i εⱼₖₗ σₗ`.
* `pauliDot_reflect` — the **reflection identity**: for a unit axis `n`,
  `(n·σ)(v·σ)(n·σ) = 2(n·v)(n·σ) − (v·σ)`, i.e. conjugation by the involution `n·σ` reflects `v` in
  the `n` axis.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **The Pauli product rule** (vector form): for real three-vectors `a`, `b`,
`(a·σ)(b·σ) = (a·b) I + i (a×b)·σ`, where `a·b` is the dot product and `a×b` the cross product.
This is the vector form of the multiplication table `σⱼσₖ = δⱼₖ I + i εⱼₖₗ σₗ`. -/
theorem pauliDot_mul (a b : Fin 3 → ℝ) :
    pauliDot a * pauliDot b
      = ((a ⬝ᵥ b : ℝ) : ℂ) • 1 + Complex.I • pauliDot (crossProduct a b) := by
  rw [pauliDot_eq, pauliDot_eq, pauliDot_eq]
  rw [cross_apply, dotProduct]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.tail_cons, smul_eq_mul] <;>
    rw [Complex.ext_iff] <;>
    constructor <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- The **conjugate transpose of the rotation operator** for a unit axis:
`R_n̂(θ)ᴴ = cos(θ/2) I + sin(θ/2) i (n·σ)`. -/
theorem rotAxis_conjTranspose_eq_of_unit {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) :
    (rotAxis n θ)ᴴ = (Real.cos (θ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + ((Real.sin (θ / 2) : ℂ) * Complex.I) • pauliDot n := by
  rw [rotAxis_eq_of_unit hn, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
    conjTranspose_one, pauliDot_conjTranspose]
  have h1 : star ((Real.cos (θ / 2) : ℂ)) = (Real.cos (θ / 2) : ℂ) := Complex.conj_ofReal _
  have h2 : star ((Real.sin (θ / 2) : ℂ) * Complex.I) = -((Real.sin (θ / 2) : ℂ) * Complex.I) := by
    rw [star_mul', ← starRingEnd_apply, ← starRingEnd_apply, Complex.conj_ofReal, Complex.conj_I,
      mul_neg]
  rw [h1, h2, neg_smul, sub_neg_eq_add]

/-- The **3D rotation** of a vector `v` by angle `θ` about the unit axis `n`, in Rodrigues form
`R(θ)v = cos θ · v + sin θ · (n × v) + (1 − cos θ)(n·v) · n`. This is the map on Bloch vectors that
the qubit rotation `R_n̂(θ)` induces. -/
noncomputable def rot3D (n : Fin 3 → ℝ) (θ : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Real.cos θ • v + Real.sin θ • crossProduct n v + ((1 - Real.cos θ) * (n ⬝ᵥ v)) • n

/-- `n ⬝ᵥ n = ‖n‖²` for the scalar norm, `= 1` for a unit vector. -/
theorem dotProduct_self_of_unit {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) : n ⬝ᵥ n = 1 := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [hn]

/-- The **anti-commutator/reflection identity** for the Pauli combination: for a unit axis `n`,
`(n·σ)(v·σ)(n·σ) = 2(n·v)(n·σ) − (v·σ)`. Geometrically, conjugating `v·σ` by the involution
`n·σ` reflects the vector `v` in the `n` axis (`v ↦ 2(n·v)n − v`). -/
theorem pauliDot_reflect {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (v : Fin 3 → ℝ) :
    pauliDot n * pauliDot v * pauliDot n
      = (2 * (n ⬝ᵥ v : ℝ) : ℂ) • pauliDot n - pauliDot v := by
  have hnn : n ⬝ᵥ n = 1 := dotProduct_self_of_unit hn
  -- (n×v)·n = 0
  have hdot : (crossProduct n v) ⬝ᵥ n = 0 := by
    rw [dotProduct_comm]; exact dot_self_cross n v
  -- (n×v)×n = v − (n·v) n
  have hcc : crossProduct (crossProduct n v) n = v - (n ⬝ᵥ v) • n := by
    rw [← cross_anticomm, cross_cross_eq_smul_sub_smul', hnn, one_smul, neg_sub]
  -- (n×v)·σ · n·σ = i (v − (n·v)n)·σ
  have hPN : pauliDot (crossProduct n v) * pauliDot n
      = Complex.I • (pauliDot v - ((n ⬝ᵥ v : ℝ) : ℂ) • pauliDot n) := by
    rw [pauliDot_mul, hdot, hcc, pauliDot_sub, pauliDot_smul]
    push_cast
    module
  rw [pauliDot_mul, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hPN, smul_smul,
    Complex.I_mul_I]
  module

/-- **The conjugation identity — the heart of Nielsen & Chuang, Exercise 4.6.** For a unit axis `n`,
conjugating the Pauli combination `v·σ` by the qubit rotation `R_n̂(θ)` is the Pauli combination
of the *rotated* vector: `R_n̂(θ) · (v·σ) · R_n̂(θ)ᴴ = (R(θ)v)·σ`, i.e. `rotAxis n θ * pauliDot
v * (rotAxis n θ)ᴴ = pauliDot (rot3D n θ v)`. -/
theorem pauliDot_conj_rotAxis {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) (v : Fin 3 → ℝ) :
    rotAxis n θ * pauliDot v * (rotAxis n θ)ᴴ = pauliDot (rot3D n θ v) := by
  have hVN : pauliDot v * pauliDot n
      = ((n ⬝ᵥ v : ℝ) : ℂ) • 1 - Complex.I • pauliDot (crossProduct n v) := by
    rw [pauliDot_mul v n, dotProduct_comm v n,
      show crossProduct v n = -crossProduct n v from (cross_anticomm n v).symm, pauliDot_neg,
      smul_neg, sub_eq_add_neg]
  have hcosR : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    have hs := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show (2 : ℝ) * (θ / 2) = θ from by ring] at h2
    linear_combination h2 + hs
  have hsinR : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  rw [rotAxis_conjTranspose_eq_of_unit hn, rotAxis_eq_of_unit hn]
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [pauliDot_reflect hn, pauliDot_mul n v, hVN, rot3D, pauliDot_add, pauliDot_add, pauliDot_smul,
    pauliDot_smul, pauliDot_smul, hcosR, hsinR]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  match_scalars
  · -- coefficient of `v·σ`: `cos²(θ/2) − sin²(θ/2) = cos θ`
    linear_combination (Complex.sin ((θ : ℂ) / 2)) ^ 2 * Complex.I_mul_I
  · -- coefficient of `1`: the two `cos(θ/2)sin(θ/2)(n·v)` terms cancel
    ring
  · -- coefficient of `(n×v)·σ`: `2 sin(θ/2)cos(θ/2) = sin θ`
    linear_combination
      (-2 * Complex.sin ((θ : ℂ) / 2) * Complex.cos ((θ : ℂ) / 2)) * Complex.I_mul_I
  · -- coefficient of `n·σ`: `2 sin²(θ/2)(n·v) = (1 − cos θ)(n·v)`, using `cos²+sin²=1`
    linear_combination
      (-2 * (Complex.sin ((θ : ℂ) / 2)) ^ 2 * ((n ⬝ᵥ v : ℝ) : ℂ)) * Complex.I_mul_I
        + ((n ⬝ᵥ v : ℝ) : ℂ) * Complex.sin_sq_add_cos_sq ((θ : ℂ) / 2)

/-- **A rotation preserves the squared length of the Bloch vector**: for a unit axis `n`, `‖R(θ)v‖²
= ‖v‖²` (with `‖·‖²` the scalar `·₀² + ·₁² + ·₂²`). The rotated Bloch vector therefore stays in
the Bloch ball. -/
theorem rot3D_sq_sum {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) (v : Fin 3 → ℝ) :
    (rot3D n θ v) 0 ^ 2 + (rot3D n θ v) 1 ^ 2 + (rot3D n θ v) 2 ^ 2
      = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  have key : pauliDot (rot3D n θ v) * pauliDot (rot3D n θ v)
      = ((v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 : ℝ) : ℂ) • 1 := by
    rw [← pauliDot_conj_rotAxis hn]
    calc rotAxis n θ * pauliDot v * (rotAxis n θ)ᴴ
            * (rotAxis n θ * pauliDot v * (rotAxis n θ)ᴴ)
        = rotAxis n θ * pauliDot v * ((rotAxis n θ)ᴴ * rotAxis n θ) * pauliDot v
            * (rotAxis n θ)ᴴ := by noncomm_ring
      _ = rotAxis n θ * (pauliDot v * pauliDot v) * (rotAxis n θ)ᴴ := by
          rw [rotAxis_conjTranspose_mul_self]; noncomm_ring
      _ = ((v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 : ℝ) : ℂ) • 1 := by
          rw [pauliDot_mul_self, mul_smul_comm, smul_mul_assoc, mul_one,
            rotAxis_mul_conjTranspose_self]
  rw [pauliDot_mul_self] at key
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) key
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  exact_mod_cast h00

end AxQM.Concrete
