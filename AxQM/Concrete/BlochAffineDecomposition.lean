/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.Basic

/-!
# Concrete: the `O S` decomposition of the Bloch affine map (`det O = 1`, `det S` unsigned)

This file supplies the mathematical content behind **Nielsen & Chuang, Exercises 8.12 and 8.14
(p. 375)** — two facts about the `M = O S` factorization (N&C (8.93)) of the Bloch affine-map
matrix.
-/

namespace AxQM.Concrete

open Matrix

/-- **Nielsen & Chuang, Exercise 8.12.** In the factorization `M = O S` of the real `3 × 3` Bloch
affine-map matrix into an orthogonal `O` and a symmetric `S` (N&C (8.93)), the orthogonal factor
may always be taken to be a *proper rotation*, `O ∈ SO(3)` (i.e. `det O = 1`), while keeping the
other factor symmetric.
-/
theorem exists_mem_specialOrthogonalGroup_symmetric_factor
    {M O S : Matrix (Fin 3) (Fin 3) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hS : Sᵀ = S) (hM : M = O * S) :
    ∃ O' S' : Matrix (Fin 3) (Fin 3) ℝ,
      O' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ S'ᵀ = S' ∧ M = O' * S' := sorry

/-- **Nielsen & Chuang, Exercise 8.14.** In the `M = O S` decomposition of the real `3 × 3` Bloch
affine-map matrix into a *proper rotation* `O ∈ SO(3)` and a symmetric `S` (N&C (8.93), with `O`
normalized to `det O = 1` as in Exercise 8.12), the symmetric factor `S` need **not** be
positive: there is such a decomposition with `det S < 0`.
-/
theorem exists_specialOrthogonalGroup_symmetric_factor_det_neg :
    ∃ M O S : Matrix (Fin 3) (Fin 3) ℝ,
      O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ Sᵀ = S ∧ M = O * S ∧ S.det < 0 := sorry

end AxQM.Concrete
