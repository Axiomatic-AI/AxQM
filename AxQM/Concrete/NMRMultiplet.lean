/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LogicalLabelingCapacity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The NMR `J`-coupling multiplet: line count and relative magnitudes (Nielsen & Chuang, Ex. 7.37)

The **second half** of Nielsen & Chuang Exercise 7.37 (§7.7, p. 329): for the Hamiltonian
`H = J Z₁(Z₂ + ⋯ + Z_{n+1})` — the observed spin `1` `J`-coupled to `n` *equivalent* neighbour spins
— the exercise asks for the number of lines in the first spin's spectrum and their relative
magnitudes. For the exercise's case `n = 3` (`H = J Z₁(Z₂+Z₃+Z₄)`) the answer is the famous
**quartet with relative magnitudes `1 : 3 : 3 : 1`**.

## Main results
* `nmrQuartet_lineCount` — for `n = 3` the collective field takes four distinct values: **four
  lines**.
* `nmrQuartet_relativeMagnitudes` — the four lines (fields `3, 1, −1, −3`) have multiplicities
  `1, 3, 3, 1`.
-/

namespace AxQM.Concrete

open scoped BigOperators

/-- **The first-spin spectrum has four lines** for `H = J Z₁(Z₂+Z₃+Z₄)` (Ex. 7.37): the collective
field takes four distinct values. -/
theorem nmrQuartet_lineCount : (Finset.image (magPop 3) Finset.univ).card = 4 := sorry

/-- **The relative magnitudes of the four lines are `1 : 3 : 3 : 1`** (Ex. 7.37). -/
theorem nmrQuartet_relativeMagnitudes :
    ([3, 1, -1, -3] : List ℤ).map
        (fun m => (Finset.univ.filter (fun A : Finset (Fin 3) => magPop 3 A = m)).card)
      = [1, 3, 3, 1] := sorry

end AxQM.Concrete
