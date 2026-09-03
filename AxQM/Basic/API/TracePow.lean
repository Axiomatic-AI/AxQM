/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Purity

/-!
# AxQM.Basic.API — the trace power `tr(ρᵏ)`

The **`k`-th trace power** `tr(ρᵏ)` of a state (Nielsen & Chuang, Exercise 8.18). It generalizes
the **purity** `tr(ρ²)`, the `k = 2` case.
-/

noncomputable section

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The **`k`-th trace power** `tr(ρᵏ)` of a state `ρ`, as a real number `re tr(ρ.op ^ k)`. Since
`ρ` is a positive operator, `ρ ^ k` is positive and its trace is real. -/
def State.traceOfPow (ρ : State S) (k : ℕ) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S.space ((ρ.op ^ k : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space))

end AxQM
