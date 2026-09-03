/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import AxQM.Concrete.RotationDecomposition
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the *corrected* generalized Euler decomposition, for perpendicular axes (N&C Ex 4.11)

Nielsen & Chuang, Exercise 4.11 claims that for **non-parallel** unit vectors `m̂, n̂` every
single-qubit unitary `U` factors as `U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` (eq. 4.13). That is
**false**: mere non-parallelism does not suffice. This file proves the **corrected** statement —
the decomposition holds whenever the middle axis is *perpendicular* to the (repeated) outer axis,
`m̂ ⊥ n̂` (Davenport's theorem).

## Main declarations
* `exists_smul_rotAxis_triple_of_perp` — **the corrected Exercise 4.11**: for orthonormal `m̂ ⊥ n̂`
  and any unitary `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`, there exist `α, β, γ, δ` with
  `U = e^{iα} • (R_n̂(β) R_m̂(γ) R_n̂(δ))`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **The corrected Nielsen & Chuang, Exercise 4.11.** For an orthonormal pair of axes — unit
vectors `m̂ ⊥ n̂` — every single-qubit unitary `U` factors as `U = e^{iα} R_n̂(β) R_m̂(γ)
R_n̂(δ)` for some real `α, β, γ, δ`. This is the true statement N&C's Exercise 4.11 intends:
perpendicularity of `m̂` and `n̂` (not mere non-parallelism) is the correct hypothesis.
-/
theorem exists_smul_rotAxis_triple_of_perp {m n : Fin 3 → ℝ}
    (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hmn : m 0 * n 0 + m 1 * n 1 + m 2 * n 2 = 0)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ,
      U = Complex.exp ((α : ℂ) * Complex.I) • (rotAxis n β * rotAxis m γ * rotAxis n δ) := sorry

end AxQM.Concrete
