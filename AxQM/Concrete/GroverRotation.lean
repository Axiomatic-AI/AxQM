/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.InversionAboutMean
import AxQM.Concrete.TwoLevelLowerBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Concrete: the Grover iteration as a 2×2 rotation (Nielsen & Chuang, Exercise 6.3)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §6.1.3 (p. 252) gives the
geometric picture of the quantum search algorithm. Writing `|α⟩` for the normalized uniform
superposition of the **non-solutions** and `|β⟩` for that of the **solutions** (Eq. 6.8–6.9),
the starting state is `|ψ⟩ = cos(θ/2)|α⟩ + sin(θ/2)|β⟩` (Eq. 6.10, with `cos(θ/2) = √((N−M)/N)`),
which lies in the plane `span{|α⟩, |β⟩}`.

## Contents

* `groverState θ` — the starting state `|ψ⟩ = cos(θ/2)|α⟩ + sin(θ/2)|β⟩` (Eq. 6.10) as a coordinate
  vector.
* `groverOracle` — the oracle restricted to `span{|α⟩,|β⟩}`, `= reflectionMatrix |α⟩` (reflection
  about `|α⟩`); `groverOracle_eq` (`= diag(1, −1)`).
* `groverIteration θ` (`= (2|ψ⟩⟨ψ| − I) O`) and `groverRotation θ` (the target matrix, Eq. 6.13).
* `groverIteration_eq_rotation` — **Exercise 6.3 (Eq. 6.13)**:
  `G = [[cos θ, −sin θ], [sin θ, cos θ]]`.
* `sin_groverAngle` — Eq. 6.14: with `cos(θ/2) = √((N−M)/N)`, `sin(θ/2) = √(M/N)` the rotation angle
  satisfies `sin θ = 2√(M(N−M))/N`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The starting state `|ψ⟩` (N&C Eq. 6.10)** written in the `|α⟩, |β⟩` basis: the coordinate
vector `cos(θ/2)|α⟩ + sin(θ/2)|β⟩` of `ℂ²`, where `|α⟩ = stdVec 0` and `|β⟩ = stdVec 1`. -/
noncomputable def groverState (θ : ℝ) : Fin 2 → ℂ :=
  (Real.cos (θ / 2) : ℂ) • stdVec 0 + (Real.sin (θ / 2) : ℂ) • stdVec 1
@[simp] theorem groverState_apply_zero (θ : ℝ) : groverState θ 0 = (Real.cos (θ / 2) : ℂ) := by
  simp [groverState, stdVec]

@[simp] theorem groverState_apply_one (θ : ℝ) : groverState θ 1 = (Real.sin (θ / 2) : ℂ) := by
  simp [groverState, stdVec]

/-- The starting state is self-conjugate (its `|α⟩, |β⟩` coordinates are real). -/
theorem star_groverState (θ : ℝ) : star (groverState θ) = groverState θ := by
  funext i
  simp only [Pi.star_apply]
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, groverState_apply_zero, groverState_apply_one,
      Complex.star_def, Complex.conj_ofReal]

/-- **The oracle on the plane `span{|α⟩, |β⟩}`** (N&C §6.1.3): the reflection about `|α⟩`,
`O = 2|α⟩⟨α| − I = reflectionMatrix |α⟩`. It fixes `|α⟩` (the non-solutions) and negates `|β⟩`
(the solutions). -/
noncomputable def groverOracle : Matrix (Fin 2) (Fin 2) ℂ :=
  reflectionMatrix (stdVec 0)

/-- The oracle's matrix in the `|α⟩, |β⟩` basis is `diag(1, −1)`. -/
theorem groverOracle_eq : groverOracle = !![1, 0; 0, -1] := by
  rw [groverOracle, reflectionMatrix, star_stdVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.vecMulVec_apply, stdVec, Pi.single_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    norm_num

/-- **The Grover iteration `G = (2|ψ⟩⟨ψ| − I) O`** (N&C, above Eq. 6.6), as a `2 × 2` matrix in the
`|α⟩, |β⟩` basis: the inversion-about-`|ψ⟩` reflection composed with the oracle. -/
noncomputable def groverIteration (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  reflectionMatrix (groverState θ) * groverOracle

/-- The `2 × 2` rotation matrix `[[cos θ, −sin θ], [sin θ, cos θ]]` (N&C Eq. 6.13). -/
noncomputable def groverRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -Real.sin θ; Real.sin θ, Real.cos θ]

/-- **The diffusion `2|ψ⟩⟨ψ| − I` in the `|α⟩, |β⟩` basis** equals
`[[cos θ, sin θ], [sin θ, −cos θ]]` (the reflection about `|ψ⟩`, at angle `θ/2` from `|α⟩`). -/
theorem reflectionMatrix_groverState (θ : ℝ) :
    reflectionMatrix (groverState θ)
      = !![(Real.cos θ : ℂ), Real.sin θ; Real.sin θ, -Real.cos θ] := by
  have hc : (Real.cos θ : ℂ) = 2 * (Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ) - 1 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show (2 : ℝ) * (θ / 2) = θ by ring] at h
    rw [h]; push_cast; ring
  have hs : (Real.sin θ : ℂ) = 2 * (Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show (2 : ℝ) * (θ / 2) = θ by ring] at h
    rw [h]; push_cast; ring
  have hc2 : -(Real.cos θ : ℂ) = 2 * (Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) - 1 := by
    have hp : (Real.sin (θ / 2) : ℂ) ^ 2 + (Real.cos (θ / 2) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq (θ / 2)
    rw [hc]; linear_combination -2 * hp
  rw [reflectionMatrix, star_groverState, hc2, hc, hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [groverState, stdVec, Matrix.one_fin_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply] <;>
    ring

/-- **Nielsen & Chuang, Exercise 6.3 (Eq. 6.13).** In the `|α⟩, |β⟩` basis the Grover iteration
`G = (2|ψ⟩⟨ψ| − I) O` is the rotation matrix `[[cos θ, −sin θ], [sin θ, cos θ]]`, where `θ` is the
angle with `|ψ⟩ = cos(θ/2)|α⟩ + sin(θ/2)|β⟩`. -/
theorem groverIteration_eq_rotation (θ : ℝ) : groverIteration θ = groverRotation θ := by
  rw [groverIteration, reflectionMatrix_groverState, groverOracle_eq, groverRotation,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **N&C Eq. 6.14.** With `cos(θ/2) = √((N−M)/N)` and `sin(θ/2) = √(M/N)` (the `M`-solution search
problem, `0 ≤ M ≤ N`), the Grover rotation angle satisfies `sin θ = 2√(M(N−M))/N`. -/
theorem sin_groverAngle (θ N M : ℝ) (hN : 0 < N) (hM : 0 ≤ M) (hMN : M ≤ N)
    (hcos : Real.cos (θ / 2) = Real.sqrt ((N - M) / N))
    (hsin : Real.sin (θ / 2) = Real.sqrt (M / N)) :
    Real.sin θ = 2 * Real.sqrt (M * (N - M)) / N := sorry

end AxQM.Concrete
