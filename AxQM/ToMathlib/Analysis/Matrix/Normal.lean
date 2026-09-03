/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# A normal matrix is Hermitian iff its spectrum is real

A *normal* complex square matrix `A` (`IsStarNormal A`, i.e. `Aᴴ * A = A * Aᴴ`) is Hermitian if and
only if every point of its spectrum — equivalently, every eigenvalue — is real.

## Main results

* `Matrix.isHermitian_iff_forall_spectrum_im_eq_zero`: for a normal `A : Matrix n n ℂ`,
  `A.IsHermitian ↔ ∀ z ∈ spectrum ℂ A, z.im = 0`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A normal matrix is Hermitian iff it has real eigenvalues** (Nielsen & Chuang, Exercise 2.17).
For a normal complex matrix `A` (`IsStarNormal A`, i.e. `Aᴴ * A = A * Aᴴ`), `A` equals its conjugate
transpose exactly when every point of its spectrum — equivalently, every eigenvalue — is real. -/
theorem isHermitian_iff_forall_spectrum_im_eq_zero {A : Matrix n n ℂ} (hA : IsStarNormal A) :
    A.IsHermitian ↔ ∀ z ∈ spectrum ℂ A, z.im = 0 := sorry

end Matrix
