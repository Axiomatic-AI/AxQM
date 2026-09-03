/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the Z–Y decomposition of a single-qubit unitary (Nielsen & Chuang, Theorem 4.1)

The **Z–Y decomposition** — **Nielsen & Chuang, Theorem 4.1** (eq. 4.11): every single-qubit
unitary `U` factors as `U = e^{iα} R_z(β) R_y(γ) R_z(δ)`, with `rotY`, `rotZ` the rotation matrices
of N&C eqs. (4.5), (4.6).

## Main declarations
* `exists_zy_decomposition` — **Theorem 4.1 itself**: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
  there exist real `α, β, γ, δ` with `U = e^{iα} • (R_z(β) R_y(γ) R_z(δ))`.
* `zyMatrixForm` — the entry-explicit matrix of N&C eq. (4.12) itself: the diagonal entries
  `e^{i(α ∓ β/2 ∓ δ/2)} cos(γ/2)` and off-diagonal `∓ e^{i(α ∓ β/2 ± δ/2)} sin(γ/2)`, with the
  global phase `e^{iα}` folded in.
* `exists_zyMatrixForm` — **Nielsen & Chuang, Exercise 4.9**: every unitary `U ∈ Matrix.unitaryGroup
  (Fin 2) ℂ` can be written in the explicit form (4.12), i.e. `∃ α β γ δ, U = zyMatrixForm α β γ δ`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Theorem 4.1 (Z–Y decomposition of a single-qubit unitary).** Every `2 × 2`
unitary `U` (a single-qubit gate, `Uᴴ U = I`) factors as `U = e^{iα} R_z(β) R_y(γ) R_z(δ)` for
some real numbers `α, β, γ, δ` (eq. 4.11). -/
theorem exists_zy_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = Complex.exp ((α : ℂ) * Complex.I) • (rotZ β * rotY γ * rotZ δ) := sorry

/-- The explicit `2 × 2` matrix of Nielsen & Chuang eq. (4.12): the Z–Y decomposition `e^{iα} R_z(β)
R_y(γ) R_z(δ)` written out entrywise, with the global phase `e^{iα}` folded into each entry.
Every entry is a phase `e^{i(α ± β/2 ± δ/2)}` times `cos(γ/2)` (diagonal) or `± sin(γ/2)`
(off-diagonal). -/
noncomputable def zyMatrixForm (α β γ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (((α : ℂ) - (β : ℂ) / 2 - (δ : ℂ) / 2) * I) * (Real.cos (γ / 2) : ℂ),
     -(Complex.exp (((α : ℂ) - (β : ℂ) / 2 + (δ : ℂ) / 2) * I) * (Real.sin (γ / 2) : ℂ));
     Complex.exp (((α : ℂ) + (β : ℂ) / 2 - (δ : ℂ) / 2) * I) * (Real.sin (γ / 2) : ℂ),
     Complex.exp (((α : ℂ) + (β : ℂ) / 2 + (δ : ℂ) / 2) * I) * (Real.cos (γ / 2) : ℂ)]

/-- **Nielsen & Chuang, Exercise 4.9.** Any single-qubit unitary `U` (a `2 × 2` complex matrix with
`Uᴴ U = I`, i.e. `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`) can be written in the explicit form
(4.12). -/
theorem exists_zyMatrixForm (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = zyMatrixForm α β γ δ := sorry

end AxQM.Concrete
