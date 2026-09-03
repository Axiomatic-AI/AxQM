/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.Hadamard

/-!
# Concrete: the X–Y decomposition of a single-qubit unitary (Nielsen & Chuang, Exercise 4.10)

Nielsen & Chuang, Exercise 4.10 (*X–Y decomposition of rotations*) asks for a decomposition
analogous to Theorem 4.1 (the Z–Y
decomposition) but using `R_x` instead of `R_z`.

## Main declarations
* `exists_xy_decomposition` — **Exercise 4.10 itself**: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
  there exist real `α, β, γ, δ` with `U = e^{iα} • (R_x(β) R_y(γ) R_x(δ))`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.10 (X–Y decomposition of a single-qubit unitary).** Every
`2 × 2` unitary `U` (a single-qubit gate, `Uᴴ U = I`) factors as `U = e^{iα} R_x(β) R_y(γ) R_x(δ)`
for some real numbers `α, β, γ, δ` — Theorem 4.1 with `R_z` replaced by `R_x`. -/
theorem exists_xy_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = Complex.exp ((α : ℂ) * Complex.I) • (rotX β * rotY γ * rotX δ) := sorry

end AxQM.Concrete
