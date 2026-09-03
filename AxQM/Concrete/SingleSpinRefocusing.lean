/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliAverage
import AxQM.Concrete.BlochRotation
import AxQM.Concrete.PauliExponential
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Concrete: three-dimensional refocusing of a single-spin Hamiltonian (Nielsen & Chuang, Ex 7.39)

Notation: `pauliDot c = c₀ X + c₁ Y + c₂ Z`.
-/

namespace AxQM.Concrete

open Matrix Complex NormedSpace
open scoped Matrix.Norms.Operator

/-- **The refocusing identity** — the answer to Exercise 7.39. Averaging any single-spin Hamiltonian
`Hsys = c·σ` over conjugation by the full Pauli pulse group `{I, X, Y, Z}` gives zero: `(c·σ) +
X (c·σ) X + Y (c·σ) Y + Z (c·σ) Z = 0`. Equivalently the equal-weight toggling-frame average `¼
Σ_P P Hsys P` vanishes — the zeroth-order average Hamiltonian is zero, so the evolution is
refocused. -/
theorem pauliDot_conjSum_eq_zero (c : Fin 3 → ℝ) :
    pauliDot c + pauliX * pauliDot c * pauliX + pauliY * pauliDot c * pauliY
      + pauliZ * pauliDot c * pauliZ = 0 := sorry

/-- **The refocusing identity using only two orthogonal pulse axes.** The refocusing of any
single-spin Hamiltonian is achieved with `π`-pulses about `x̂` and `ŷ` alone:
`(c·σ) + X (c·σ) X + Y (c·σ) Y + X (Y (c·σ) Y) X = 0`. This is the concrete "two orthogonal axes"
answer to Exercise 7.39. -/
theorem pauliDot_conjSum_twoAxis_eq_zero (c : Fin 3 → ℝ) :
    pauliDot c + pauliX * pauliDot c * pauliX + pauliY * pauliDot c * pauliY
      + pauliX * (pauliY * pauliDot c * pauliY) * pauliX = 0 := sorry

end AxQM.Concrete
