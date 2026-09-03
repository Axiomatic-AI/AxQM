/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# An orthogonal pair in `ℂ²` and its normalized forms (Nielsen & Chuang, Exercise 2.7)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.7
(p. 66) asks to verify that the vectors `|w⟩ ≡ (1, 1)` and `|v⟩ ≡ (1, -1)` of
`ℂ²` are *orthogonal*, and to find their *normalized forms*.
-/

namespace AxQM.Concrete

open scoped ComplexConjugate

/-- The vector `|w⟩ ≡ (1, 1)` of `ℂ²` from Nielsen & Chuang, Exercise 2.7.
`ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)`. -/
def vecOneOneC2 : EuclideanSpace ℂ (Fin 2) := !₂[1, 1]

/-- The vector `|v⟩ ≡ (1, -1)` of `ℂ²` from Nielsen & Chuang, Exercise 2.7.
`ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)`. -/
def vecOneNegOneC2 : EuclideanSpace ℂ (Fin 2) := !₂[1, -1]

/-- **Nielsen & Chuang, Exercise 2.7 (orthogonality).** The vectors `(1, 1)`
and `(1, -1)` of `ℂ²` are orthogonal: their inner product (N&C `(2.14)`,
`(y, z) = ∑ᵢ yᵢ* zᵢ`) is `0`. -/
theorem inner_vecOneOneC2_vecOneNegOneC2_eq_zero :
    inner ℂ vecOneOneC2 vecOneNegOneC2 = 0 := sorry

/-- The normalized form of `(1, 1)`, namely `(1/√2, 1/√2)`. -/
noncomputable def unitVecOneOneC2 : EuclideanSpace ℂ (Fin 2) :=
  !₂[(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹]

/-- The normalized form of `(1, -1)`, namely `(1/√2, -1/√2)`. -/
noncomputable def unitVecOneNegOneC2 : EuclideanSpace ℂ (Fin 2) :=
  !₂[(Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- **Nielsen & Chuang, Exercise 2.7 (normalized form of `(1, 1)`).** The
explicit vector `(1/√2, 1/√2)` is the normalized form `|v⟩/‖v⟩‖` of `(1, 1)`. -/
theorem unitVecOneOneC2_eq_norm_inv_smul :
    unitVecOneOneC2 = (‖vecOneOneC2‖ : ℂ)⁻¹ • vecOneOneC2 := sorry

/-- **Nielsen & Chuang, Exercise 2.7 (normalized form of `(1, -1)`).** The
explicit vector `(1/√2, -1/√2)` is the normalized form `|v⟩/‖v⟩‖` of `(1, -1)`. -/
theorem unitVecOneNegOneC2_eq_norm_inv_smul :
    unitVecOneNegOneC2 = (‖vecOneNegOneC2‖ : ℂ)⁻¹ • vecOneNegOneC2 := sorry

end AxQM.Concrete
