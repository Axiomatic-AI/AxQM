/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# AxQM — the fidelity generator (Nielsen & Chuang §9.2.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.2.2
(equation `(9.53)`, p. 409) define the **fidelity** between two states `ρ` and
`σ` as
```
F(ρ, σ) ≡ tr √(√ρ σ √ρ),
```
the trace of the positive square root of `√ρ · σ · √ρ`. It is a second measure
of distance between quantum states (alongside the trace distance,
`State.traceDistance`) and — as N&C develop across §9.2.2 — underlies a genuine
metric (the angle `A(ρ,σ) = arccos F(ρ,σ)`).

## Main definitions

* `State.fidelity` — the fidelity `tr √(√ρ σ √ρ)` of N&C `(9.53)`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **fidelity** between two states `ρ` and `σ` of the system `S`, Nielsen & Chuang `(9.53)`:
`F(ρ, σ) ≡ tr √(√ρ σ √ρ)`, the trace of the positive square root of `√ρ · σ · √ρ`. -/
noncomputable def State.fidelity (ρ σ : State S) : ℝ :=
  RCLike.re ((LinearMap.trace ℂ S.space)
    ↑(cfc Real.sqrt (cfc Real.sqrt ρ.op * σ.op * cfc Real.sqrt ρ.op)))

end AxQM
