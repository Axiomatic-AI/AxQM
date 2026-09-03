/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.Evolution

/-!
# AxQM.Basic.API — the inverse quantum Fourier transform as a unitary evolution

The **wrapper** for Nielsen & Chuang **Exercise 5.5**, which asks for a circuit performing the
inverse quantum Fourier transform. The quantum Fourier transform `F` is realized as a
unitary `Evolution` (`qftEvolution d`, built for Problem 5.1); its inverse `F⁻¹` is a unitary
transformation too, so it is itself an implementable circuit — the *adjoint* (inverse) gate `F†`.
This file packages `F⁻¹` and computes its action, mirroring the QFT development.

## Main declarations
* `qftInverseEvolution d` — the **inverse QFT as a unitary `Evolution (qudit d)`**, defined as the
  adjoint `(qftEvolution d).adjoint = F†`. Because `Evolution.adjoint` is again a unitary
  `Evolution`, the very existence of this term is the exercise's answer: the inverse transform *is*
  a legitimate quantum circuit, the adjoint of the QFT circuit (which, gate for gate, is the QFT
  circuit run in reverse with each gate daggered).
* `qftInverseEvolution_op_eq` — its operator is `toEuclideanCLM` of the **conjugate-transpose** QFT
  matrix, `F† = toEuclideanCLM (qftMatrix d)ᴴ`, since `Matrix.toEuclideanCLM` is a star-algebra
  equivalence (adjoint of operator ↔ conjugate transpose of matrix).
* `qftInverseEvolution_op_apply_quditBasis` — the **inverse-transform action**
  `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`: the inverse discrete Fourier transform, the conjugate of
  the forward action.
* `qftInverseFourierImage d k` — that image state `∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩` as a `PureState`
  (normalized, being the image of a unit vector under the unitary `F†`).
-/

noncomputable section

namespace AxQM

open AxQM.Concrete
open scoped Matrix

/-- The **inverse quantum Fourier transform on `qudit d`** as a unitary `Evolution` , defined as the
adjoint (inverse) gate of the QFT evolution: `F⁻¹ = F† = (qftEvolution d).adjoint`. Since a
unitary's adjoint is again unitary, this is a genuine `Evolution` — an implementable quantum
circuit — realizing the inverse transform. -/
def qftInverseEvolution (d : ℕ) [NeZero d] : Evolution (qudit d) := (qftEvolution d).adjoint

/-- The underlying operator of `qftInverseEvolution d` is the Hilbert-space adjoint of the QFT
operator, `F† = adjoint (toEuclideanCLM (qftMatrix d))`. -/
@[simp]
theorem qftInverseEvolution_op (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).op
      = ContinuousLinearMap.adjoint
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d)) := rfl

/-- The inverse QFT operator is `toEuclideanCLM` of the **conjugate-transpose** QFT matrix,
`F† = toEuclideanCLM (qftMatrix d)ᴴ`. Because `Matrix.toEuclideanCLM` is a star-algebra equivalence
(`star` on operators is the adjoint, `star` on matrices is the conjugate transpose), the adjoint of
`toEuclideanCLM (qftMatrix d)` is `toEuclideanCLM` of `star (qftMatrix d) = (qftMatrix d)ᴴ`. -/
theorem qftInverseEvolution_op_eq (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d)ᴴ := by
  rw [qftInverseEvolution_op, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    Matrix.star_eq_conjTranspose]

/-- **Action of the inverse QFT on a computational-basis state, compact form:** `F⁻¹|k⟩ = ∑ⱼ (Fᴴ)ⱼₖ
|j⟩`, the `k`-th column of the conjugate-transpose matrix `(qftMatrix d)ᴴ`. -/
theorem qftInverseEvolution_op_apply_quditBasis_matrix (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseEvolution d).op (quditBasis k).vec
      = ∑ j : Fin d, ((qftMatrix d)ᴴ j k) • (quditBasis j).vec := by
  rw [qftInverseEvolution_op_eq]
  exact Matrix.toEuclideanCLM_apply_single (qftMatrix d)ᴴ k

/-- **Action of the inverse QFT on a computational-basis state** (Nielsen & Chuang Exercise 5.5, the
inverse of eq. 5.2): `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`. -/
theorem qftInverseEvolution_op_apply_quditBasis (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseEvolution d).op (quditBasis k).vec
      = ∑ j : Fin d, ((Real.sqrt d : ℂ)⁻¹
          * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)))
          • (quditBasis j).vec := by
  rw [qftInverseEvolution_op_apply_quditBasis_matrix]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [qftMatrix_conjTranspose_apply]

/-- The **inverse quantum Fourier image state** `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩` of the
computational-basis state `|k⟩`, as a `PureState` of `qudit d`. -/
def qftInverseFourierImage (d : ℕ) [NeZero d] (k : Fin d) : PureState (qudit d) where
  vec := ∑ j : Fin d, ((Real.sqrt d : ℂ)⁻¹
      * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d))) • (quditBasis j).vec
  normalized := by
    rw [← qftInverseEvolution_op_apply_quditBasis d k, (qftInverseEvolution d).norm_op_apply]
    exact (quditBasis k).normalized

end AxQM
