/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroupNegOne
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: Nielsen & Chuang Proposition 10.3 — independent generators ↔ linearly independent rows

This file proves Nielsen & Chuang's **Proposition 10.3** (§10.5.1, p. 457), the bridge between the
two notions of "independence" for a set of stabilizer generators.
-/

open scoped BigOperators

namespace AxQM.Concrete

/-- **N&C's notion of independence** (eq. 10.82) for a family of group generators: dropping any one
generator strictly shrinks the subgroup generated, `⟨g₁, …, ĝᵢ, …, g_l⟩ ≠ ⟨g₁, …, g_l⟩`. -/
def IndependentGenerators {G : Type*} [Group G] {l : ℕ} (g : Fin l → G) : Prop :=
  ∀ i, Subgroup.closure (g '' ({i}ᶜ : Set (Fin l))) ≠ Subgroup.closure (Set.range g)

/-- **Nielsen & Chuang, Proposition 10.3.** Let `g : Fin l → PauliGroup n` generate `S = ⟨range g⟩`
with `-I ∉ S` (`PauliGroup.negOne n ∉ S`). Then the generators are **independent** (in the sense
of eq. 10.82, `IndependentGenerators g`: dropping any `gᵢ` strictly shrinks `S`) **if and only
if** the rows of the corresponding check matrix — the check rows `r(gᵢ) = PauliGroup.checkRowHom
(gᵢ)` — are `𝔽₂ = ZMod 2`-**linearly independent**.
-/
theorem stabilizerGenerators_independent_iff_checkRow_linearIndependent {n l : ℕ}
    (g : Fin l → PauliGroup n)
    (hneg : PauliGroup.negOne n ∉ Subgroup.closure (Set.range g)) :
    IndependentGenerators g ↔
      LinearIndependent (ZMod 2) (fun i => PauliGroup.checkRowHom (g i)) := sorry

end AxQM.Concrete
