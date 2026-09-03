/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Basic.API — the group system `ℂ[G]`

The quantum register on a finite group `G`, whose state space is the group algebra `ℂ[G]`
(Nielsen & Chuang, Problem 5.5, the non-Abelian hidden subgroup problem).
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The **group quantum system** on `G`: the system whose state space is the group algebra
`ℂ[G] = EuclideanSpace ℂ G`, with computational basis `{|g⟩}_{g ∈ G}`. It is the register the
Nielsen & Chuang Problem 5.5 query state (5.80) lives on; `qudit d` is the special case
`G = Fin d`. Only the finiteness of `G` is used here. -/
def groupSystem (G : Type*) [Fintype G] : QSystem := QSystem.ofModel (EuclideanSpace ℂ G)

/-- The **dimension of the group system is `|G|`**: `finrank ℂ (EuclideanSpace ℂ G) = |G|`. This is
the `|G|` in the Problem 5.5 success bound `1 - 1/|G|`. -/
theorem groupSystem_dim (G : Type*) [Fintype G] : (groupSystem G).dim = Fintype.card G := by
  rw [QSystem.dim]
  change Module.finrank ℂ (EuclideanSpace ℂ G) = _
  rw [finrank_euclideanSpace]

end AxQM
