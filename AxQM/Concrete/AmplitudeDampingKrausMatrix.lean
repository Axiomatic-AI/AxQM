/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix

/-!
# Concrete: the amplitude-damping Kraus matrices

The two `2 × 2` complex **operation elements** of the single-qubit amplitude-damping channel with
damping parameter `γ` (Nielsen & Chuang eq. 10.46, §8.3.5).
-/

open Matrix

namespace AxQM.Concrete

/-- The **first amplitude-damping Kraus matrix** `E₀ = !![1, 0; 0, √(1-γ)]` (Nielsen & Chuang
eq. 10.46): it leaves the ground state `|0⟩` fixed and damps the amplitude of `|1⟩` by `√(1-γ)`. -/
noncomputable def ampDampKrausMatrixZero (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (Real.sqrt (1 - γ) : ℂ)]

/-- The **second amplitude-damping Kraus matrix** `E₁ = !![0, √γ; 0, 0] = √γ |0⟩⟨1|` (Nielsen &
Chuang eq. 10.46): the `|1⟩ → |0⟩` decay with amplitude `√γ`. -/
noncomputable def ampDampKrausMatrixOne (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.sqrt γ : ℂ); 0, 0]

/-- The **amplitude-damping Kraus family** `![E₀, E₁]` (Nielsen & Chuang eq. 10.46), the `Fin 2`
bundle of `ampDampKrausMatrixZero`, `ampDampKrausMatrixOne`. -/
noncomputable def amplitudeDampingKrausMatrix (γ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => ampDampKrausMatrixZero γ
  | 1 => ampDampKrausMatrixOne γ

/-- The conjugate transpose of `E₀` is `E₀` itself. -/
theorem ampDampKrausMatrixZero_conjTranspose (γ : ℝ) :
    (ampDampKrausMatrixZero γ)ᴴ = ampDampKrausMatrixZero γ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ampDampKrausMatrixZero, Matrix.conjTranspose_apply]

/-- The conjugate transpose of `E₁ = √γ |0⟩⟨1|` is `√γ |1⟩⟨0| = !![0, 0; √γ, 0]`. -/
theorem ampDampKrausMatrixOne_conjTranspose (γ : ℝ) :
    (ampDampKrausMatrixOne γ)ᴴ = !![0, 0; (Real.sqrt γ : ℂ), 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ampDampKrausMatrixOne, Matrix.conjTranspose_apply]

/-- **The two-term completeness relation** `E₀† E₀ + E₁† E₁ = I` (`0 ≤ γ ≤ 1`). -/
theorem ampDampKrausMatrix_completeness_two (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (ampDampKrausMatrixZero γ)ᴴ * ampDampKrausMatrixZero γ
        + (ampDampKrausMatrixOne γ)ᴴ * ampDampKrausMatrixOne γ = 1 := by
  have ht : (↑(Real.sqrt (1 - γ)) : ℂ) * ↑(Real.sqrt (1 - γ)) = 1 - (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hu : (↑(Real.sqrt γ) : ℂ) * ↑(Real.sqrt γ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [ampDampKrausMatrixZero_conjTranspose, ampDampKrausMatrixOne_conjTranspose,
    ampDampKrausMatrixZero, ampDampKrausMatrixOne, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    push_cast
  · ring
  · ring
  · ring
  · linear_combination ht + hu

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the amplitude-damping Kraus family
(`0 ≤ γ ≤ 1`), certifying trace preservation. -/
theorem amplitudeDampingKrausMatrix_completeness (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ∑ i, (amplitudeDampingKrausMatrix γ i)ᴴ * amplitudeDampingKrausMatrix γ i = 1 := by
  rw [Fin.sum_univ_two]
  exact ampDampKrausMatrix_completeness_two γ h0 h1

end AxQM.Concrete
