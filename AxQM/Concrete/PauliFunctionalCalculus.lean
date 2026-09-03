/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Matrix.Spectrum
import AxQM.Concrete.Pauli
import AxQM.ToMathlib.Analysis.RCLike.Basic

/-!
# Concrete: functions of the Pauli combination `θ n·σ` (Nielsen & Chuang, Problem 2.1)

**Nielsen & Chuang, Problem 2.1 ("Functions of the Pauli matrices")**: the value of `f(θ n·σ)`
for any function `f : ℂ → ℂ`, real angle `θ`, and normalized real three-vector `n`.
-/

namespace AxQM.Concrete

open Matrix Complex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The **spectral functional calculus** of a Hermitian matrix for a complex-valued function `f : ℂ
→ ℂ`: the triple product `U · diagonal (f ∘ eigenvalues) · U†` from the spectral theorem,
evaluating `f` at the (coerced) real eigenvalues. -/
noncomputable def functionOfHermitian {A : Matrix m m ℂ} (hA : A.IsHermitian)
    (f : ℂ → ℂ) : Matrix m m ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ)) hA.eigenvectorUnitary
    (Matrix.diagonal fun i => f (hA.eigenvalues i))

/-- `θ • (n·σ)` is Hermitian. -/
theorem pauliDot_smul_isHermitian (θ : ℝ) (n : Fin 3 → ℝ) :
    ((θ : ℂ) • pauliDot n).IsHermitian :=
  (pauliDot_isHermitian n).smul (RCLike.isSelfAdjoint_ofReal θ)

/-- **Nielsen & Chuang, Problem 2.1 (Functions of the Pauli matrices).** For any
`f : ℂ → ℂ`, real `θ`, and normalized real three-vector `n`,

`f(θ n·σ) = ((f(θ) + f(-θ))/2) I + ((f(θ) - f(-θ))/2) n·σ`.

Here `f(θ n·σ)` is the spectral functional calculus `functionOfHermitian` of the
Hermitian matrix `θ • (n·σ)`. -/
theorem functionOfPauliDot_decomposition (f : ℂ → ℂ) (θ : ℝ) {n : Fin 3 → ℝ}
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    functionOfHermitian (pauliDot_smul_isHermitian θ n) f =
      ((f θ + f (-θ)) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((f θ - f (-θ)) / 2) • pauliDot n := sorry

end AxQM.Concrete
