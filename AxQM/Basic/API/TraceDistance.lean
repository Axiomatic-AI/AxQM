/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# AxQM — the quantum trace distance generator (Nielsen & Chuang §9.2.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.2.1
(equation `(9.11)`, p. 403) define the **trace distance** between two states
`ρ` and `σ` as
```
D(ρ, σ) ≡ ½ tr|ρ − σ| = ½ ‖ρ − σ‖₁,
```
half the trace norm of the difference of their density operators. It is the
quantum generalization of the classical trace distance
`AxQM.Concrete.classicalTraceDist` (N&C `(9.1)`), and — as N&C stress in
§9.2.1 — it is a genuine *metric* on the space of density operators.

## Main definitions

* `State.traceDistance` — the trace distance `½ ‖ρ − σ‖₁` of N&C `(9.11)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **quantum trace distance** between two states `ρ` and `σ` of the system `S`, Nielsen &
Chuang `(9.11)`: `D(ρ, σ) ≡ ½ tr|ρ − σ| = ½ ‖ρ − σ‖₁`, half the trace norm of the difference of
their density operators. -/
noncomputable def State.traceDistance (ρ σ : State S) : ℝ :=
  (ρ.op - σ.op).traceNorm / 2

end AxQM
