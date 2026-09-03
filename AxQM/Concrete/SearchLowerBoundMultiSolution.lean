/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# The multiple-solution quantum search oracle

*(Supports Nielsen & Chuang, Exercise 6.17 — "Optimality for multiple solutions", N&C p. 271.)*
-/

open scoped BigOperators InnerProductSpace
open Finset InnerProductSpace

namespace AxQM.Concrete

noncomputable section

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The marked projection `P_s`: the orthogonal projection onto the span of the marked basis vectors
`{b y : y ∈ s}` (N&C eq. (2.35)). -/
def markedProj (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) : H →L[ℂ] H :=
  orthonormalProjector ℂ (⇑b) s

/-- The search oracle `O_s = I − 2 P_s`: the reflection phase-flipping the marked items, as a
continuous linear map. -/
def markedOracle (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 : ℂ) • markedProj b s

end

end AxQM.Concrete
