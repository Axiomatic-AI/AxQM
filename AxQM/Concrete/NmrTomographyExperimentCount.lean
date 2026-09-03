/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import AxQM.Concrete.DensityMatrixRealDimension

/-!
# Concrete: how many NMR tomography experiments for `n` spins (Nielsen & Chuang, Exercise 7.46)

**Nielsen & Chuang, Exercise 7.46** (p. 337, §7.7.4) — how many tomography experiments are
sufficient, and how many necessary, for three spins.
-/

open Matrix
open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- A **measurement setting** `s : Fin n → Fin 3` (one of three bases `{Z, Y, X}` per spin, realized
by the pre-pulses `{I, R_x, R_y}`) **observes** the Pauli string `g : Fin n → Fin 4` when each of
`g`'s non-identity factors matches that spin's measured basis: `∀ i, g i = 0 ∨ g i = (s i).succ`.
The three non-identity Pauli indices `1, 2, 3 : Fin 4` are the images `(·).succ` of the three
bases `0, 1, 2 : Fin 3`; a factor `g i = 0` (identity) is observed under any basis. -/
def SettingObserves (s : Fin n → Fin 3) (g : Fin n → Fin 4) : Prop :=
  ∀ i, g i = 0 ∨ g i = (s i).succ

/-- A finite family of settings `T` is **tomographically complete** when every non-identity Pauli
string `g` is observed by some setting in `T`. This is the precise reading of `T` supplying enough
data to reconstruct `ρ`. -/
def TomographyComplete (T : Finset (Fin n → Fin 3)) : Prop :=
  ∀ g : Fin n → Fin 4, g ≠ 0 → ∃ s ∈ T, SettingObserves s g

/-- **Sufficiency.** The full family of all `3ⁿ` settings is tomographically complete. For three
spins this is the `27`-experiment scheme. -/
theorem tomographyComplete_univ :
    TomographyComplete (Finset.univ : Finset (Fin n → Fin 3)) := sorry

/-- **The number of NMR tomography experiments for `n` spins**. -/
def nmrTomographyExperiments (n : ℕ) : ℕ := 3 ^ n

/-- **The count.** For `0 < n` spins, any tomographically complete family has exactly
`nmrTomographyExperiments n = 3ⁿ` settings: `3ⁿ` experiments are both sufficient and necessary. -/
theorem TomographyComplete.card_eq (hn : 0 < n) {T : Finset (Fin n → Fin 3)}
    (hT : TomographyComplete T) : T.card = nmrTomographyExperiments n := sorry

/-- **Exercise 7.46, sufficient & necessary count.** Three spins: `3³ = 27` experiments. -/
theorem nmrTomographyExperiments_three : nmrTomographyExperiments 3 = 27 := sorry

end AxQM.Concrete
