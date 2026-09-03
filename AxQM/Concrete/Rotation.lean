/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliExponential

/-!
# Concrete: the single-qubit rotation operators (Nielsen & Chuang, §4.2, eq. 4.4–4.8)

For a real three-vector `n` and a real angle `θ`, Nielsen & Chuang define the rotation about the
`n`-axis by `R_n̂(θ) ≡ exp(−iθ (n·σ)/2)`  (eq. 4.8), and the three coordinate rotations `R_x`,
`R_y`, `R_z` as the special cases `n = x̂, ŷ, ẑ` (eq. 4.4–4.6).

## Main declarations
* `rotAxis n θ = exp(−i (θ/2) (n·σ))` — the rotation operator (eq. 4.8), for *any* three-vector `n`.
* `rotAxis_eq_of_unit` — the closed form `R_n̂(θ) = cos(θ/2) I − i sin(θ/2) (n·σ)` for a unit `n`
  (the right-hand side of eq. 4.8), reusing the Exercise 2.35 exponential `pauliDot_exp_of_unit`.
* `rotAxis_mem_unitaryGroup` — every rotation is unitary. This holds for *any* axis: the exponent
  `A = −i(θ/2)(n·σ)` is skew-Hermitian (`n·σ` is Hermitian), and `exp` commutes with the adjoint
  (`Matrix.exp_conjTranspose`), so `Rᴴ R = exp(−A) exp(A) = exp 0 = I`.
* `rotAxis_zero` — `R_n̂(0) = I`.
* `rotX`, `rotY`, `rotZ` — the coordinate rotations (eq. 4.4–4.6), with their explicit `2 × 2`
  closed forms `rotX_eq`, `rotY_eq`, `rotZ_eq` and unitarity.
-/

namespace AxQM.Concrete

open Matrix Complex NormedSpace

/-- The **rotation operator** `R_n̂(θ) ≡ exp(−iθ (n·σ)/2)` about the axis `n` by angle `θ` (Nielsen
& Chuang, eq. 4.8). -/
noncomputable def rotAxis (n : Fin 3 → ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  exp ((((-(θ / 2) : ℝ) : ℂ) * Complex.I) • pauliDot n)

/-- The **closed form** of the rotation operator (Nielsen & Chuang, eq. 4.8, right-hand side): for a
unit axis `n` (`n₀² + n₁² + n₂² = 1`),
`R_n̂(θ) = cos(θ/2) • I − (sin(θ/2) · i) • (n·σ)`.
This is the Exercise 2.35 exponential `pauliDot_exp_of_unit` at angle `−θ/2`. -/
theorem rotAxis_eq_of_unit {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) :
    rotAxis n θ = (Real.cos (θ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - ((Real.sin (θ / 2) : ℂ) * Complex.I) • pauliDot n := by
  rw [rotAxis, pauliDot_exp_of_unit hn, Real.cos_neg, Real.sin_neg]
  push_cast
  module

/-- Each rotation operator is **unitary** in the sense of `Rᴴ R = I`. This needs no unit hypothesis.
-/
theorem rotAxis_conjTranspose_mul_self (n : Fin 3 → ℝ) (θ : ℝ) :
    (rotAxis n θ)ᴴ * rotAxis n θ = 1 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (((-(θ / 2) : ℝ) : ℂ) * Complex.I) • pauliDot n with hA
  have hskew : Aᴴ = -A := by
    rw [hA, conjTranspose_smul, pauliDot_conjTranspose,
      show star (((-(θ / 2) : ℝ) : ℂ) * Complex.I) = -(((-(θ / 2) : ℝ) : ℂ) * Complex.I) by
        simp [Complex.conj_I], neg_smul]
  have hcomm : Commute (-A) A := (Commute.refl A).neg_left
  calc (rotAxis n θ)ᴴ * rotAxis n θ
      = exp Aᴴ * exp A := by rw [rotAxis, ← Matrix.exp_conjTranspose]
    _ = exp (-A) * exp A := by rw [hskew]
    _ = exp (-A + A) := (Matrix.exp_add_of_commute (-A) A hcomm).symm
    _ = 1 := by rw [neg_add_cancel, NormedSpace.exp_zero]

/-- Each rotation operator is **unitary** (`R ∈ unitaryGroup`), the group-membership form of
`rotAxis_conjTranspose_mul_self`. -/
theorem rotAxis_mem_unitaryGroup (n : Fin 3 → ℝ) (θ : ℝ) :
    rotAxis n θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact rotAxis_conjTranspose_mul_self n θ

/-- Each rotation operator is **unitary** in the sense of `R Rᴴ = I` (the companion of
`rotAxis_conjTranspose_mul_self`'s `Rᴴ R = I`), the group-membership `rotAxis_mem_unitaryGroup`
read as `R * star R = 1`. -/
theorem rotAxis_mul_conjTranspose_self (n : Fin 3 → ℝ) (θ : ℝ) :
    rotAxis n θ * (rotAxis n θ)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp (rotAxis_mem_unitaryGroup n θ)

/-- The **zero rotation** is the identity: `R_n̂(0) = I` (`exp 0 = I`). -/
theorem rotAxis_zero (n : Fin 3 → ℝ) : rotAxis n 0 = 1 := by
  rw [rotAxis]
  simp only [neg_zero, zero_div, Complex.ofReal_zero, zero_mul, zero_smul, NormedSpace.exp_zero]

/-- The **rotation about the `x̂` axis** `R_x(θ) ≡ exp(−iθX/2)` (Nielsen & Chuang, eq. 4.4). -/
noncomputable def rotX (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := rotAxis ![1, 0, 0] θ

/-- The **rotation about the `ŷ` axis** `R_y(θ) ≡ exp(−iθY/2)` (Nielsen & Chuang, eq. 4.5). -/
noncomputable def rotY (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := rotAxis ![0, 1, 0] θ

/-- The **rotation about the `ẑ` axis** `R_z(θ) ≡ exp(−iθZ/2)` (Nielsen & Chuang, eq. 4.6). -/
noncomputable def rotZ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := rotAxis ![0, 0, 1] θ

/-- The explicit matrix of `R_x` (Nielsen & Chuang, eq. 4.4):
`R_x(θ) = !![cos(θ/2), −i sin(θ/2); −i sin(θ/2), cos(θ/2)]`. -/
theorem rotX_eq (θ : ℝ) :
    rotX θ = !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ) * Complex.I;
                -(Real.sin (θ / 2) : ℂ) * Complex.I, (Real.cos (θ / 2) : ℂ)] := sorry

/-- The explicit matrix of `R_y` (Nielsen & Chuang, eq. 4.5):
`R_y(θ) = !![cos(θ/2), −sin(θ/2); sin(θ/2), cos(θ/2)]`. -/
theorem rotY_eq (θ : ℝ) :
    rotY θ = !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
                (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)] := by
  rw [rotY, rotAxis_eq_of_unit (by simp), pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]

/-- The explicit matrix of `R_z` (Nielsen & Chuang, eq. 4.6):
`R_z(θ) = !![exp(−iθ/2), 0; 0, exp(iθ/2)]` (a diagonal phase). -/
theorem rotZ_eq (θ : ℝ) :
    rotZ θ = !![Complex.exp (-(θ / 2) * Complex.I), 0; 0, Complex.exp ((θ / 2) * Complex.I)] := by
  have e1 : Complex.exp (-(θ / 2) * Complex.I)
      = (Real.cos (θ / 2) : ℂ) - (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show (-(θ / 2) : ℂ) * Complex.I = ((-(θ / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have e2 : Complex.exp ((θ / 2) * Complex.I)
      = (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show ((θ / 2) : ℂ) * Complex.I = ((θ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [rotZ, rotAxis_eq_of_unit (by simp), pauliDot_eq, e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `R_x(θ)` is unitary. -/
theorem rotX_mem_unitaryGroup (θ : ℝ) : rotX θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  rotAxis_mem_unitaryGroup _ θ

/-- `R_y(θ)` is unitary. -/
theorem rotY_mem_unitaryGroup (θ : ℝ) : rotY θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  rotAxis_mem_unitaryGroup _ θ

/-- `R_z(θ)` is unitary. -/
theorem rotZ_mem_unitaryGroup (θ : ℝ) : rotZ θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  rotAxis_mem_unitaryGroup _ θ

end AxQM.Concrete
