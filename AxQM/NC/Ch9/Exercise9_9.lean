/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.Density
import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-!
# Nielsen & Chuang, Exercise 9.9 (Existence of fixed points)

*(N&C p. 408.)*

Use Schauder fixed-point theorem to show any trace-preserving quantum op has a fixed point.

* `exists_fixedPoint` — every channel `f` of a system that has states fixes some state: `∃ ρ, f ρ =
  ρ`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.9 (Existence of fixed points).** Every trace-preserving quantum
operation `f` (a `AxQM.IsChannel`) of a system that has states fixes some state. -/
theorem IsChannel.exists_fixedPoint [Nonempty (State S)] {f : State S → State S}
    (hf : IsChannel f) : ∃ ρ : State S, f ρ = ρ := sorry

end AxQM
