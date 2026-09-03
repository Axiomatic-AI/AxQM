/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TraceDistance
import AxQM.Basic.API.QuantumChannel

/-!
# Nielsen & Chuang, Theorem 9.2 (Trace-preserving quantum operations are contractive)

*(N&C p. 406.)*

Trace-preserving quantum operations are contractive: D(E(rho),E(sigma))<=D(rho,sigma).

* `traceDistance_channel_le` — `D(f ρ, f σ) ≤ D(ρ, σ)` for every channel `f` and all states `ρ`,
  `σ`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Trace-preserving quantum operations are contractive** (Nielsen & Chuang, Theorem 9.2,
`(9.35)`). A quantum channel `f` never increases the trace distance: `D(f ρ, f σ) ≤ D(ρ, σ)` for all
states `ρ`, `σ`. -/
theorem traceDistance_channel_le {f : State S → State S} (hf : IsChannel f) (ρ σ : State S) :
    (f ρ).traceDistance (f σ) ≤ ρ.traceDistance σ := sorry

end AxQM
