/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerConcatenation
import AxQM.Concrete.StabilizerCodeDimension

/-! # Concatenated stabilizer codes have parameters `[n₁n₂, 1]` (Nielsen & Chuang, Exercise 10.62)

From an inner `[n₁, 1]` code `C₁ : StabCode1 g₁` (`n₁ = g₁ + 1`) and an outer `[n₂, 1]` code
`C₂ : StabCode1 g₂` (`n₂ = g₂ + 1`), the explicit concatenated generator family
`concatGen C₁ C₂ : ConcatIdx g₁ g₂ → (Fin (n₁n₂) → Fin 4)` lives on `n₁n₂ = (g₂+1)(g₁+1)` qubits.
-/

namespace AxQM.Concrete

variable {g₁ g₂ : ℕ}

/-- The bijection `ConcatIdx g₁ g₂ ≃ Fin (n₁n₂ − 1)` obtained from the generator count
`concatIdx_card` (`Fintype.card (ConcatIdx g₁ g₂) = (g₂+1)(g₁+1) − 1`). Noncomputable: it is a
choice-extracted enumeration of the index set. -/
noncomputable def concatIdxEquivFin : ConcatIdx g₁ g₂ ≃ Fin ((g₂ + 1) * (g₁ + 1) - 1) :=
  Fintype.equivFinOfCardEq concatIdx_card

/-- **The concatenated generators reindexed onto `Fin (n₁n₂ − 1)`.** This is `concatGen` composed
with the enumeration `concatIdxEquivFin`, so that the family has the `Fin (n − k)`-index shape
(`n = n₁n₂`, `k = 1`). -/
noncomputable def concatGenFin (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    Fin ((g₂ + 1) * (g₁ + 1) - 1) → (Fin ((g₂ + 1) * (g₁ + 1)) → Fin 4) :=
  fun j => concatGen C₁ C₂ (concatIdxEquivFin.symm j)

/-- **Nielsen & Chuang, Exercise 10.62.** Concatenating an inner `[n₁, 1]` stabilizer code `C₁` (`n₁
= g₁ + 1`) with an outer `[n₂, 1]` code `C₂` (`n₂ = g₂ + 1`) yields an `[n₁n₂, 1]` code: on the
`n₁n₂ = (g₂+1)(g₁+1)`-qubit register, the `n₁n₂ − 1` commuting, `𝔽₂`-independent concatenated
generators (`concatGenFin`) stabilize a code space of dimension `2 = 2¹`, i.e. exactly `k = 1`
encoded qubit.
-/
theorem concat_stabilizedSubspace_finrank (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    Module.finrank ℂ (stabilizedSubspace (concatGenFin C₁ C₂)) = 2 := sorry

end AxQM.Concrete
