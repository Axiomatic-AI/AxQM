/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.QuantumChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation

/-!
# Nielsen & Chuang, Theorem 9.6 (Monotonicity of the fidelity)

*(N&C p. 414.)*

Monotonicity of fidelity: F(E(rho),E(sigma))>=F(rho,sigma) for trace-preserving E.

* `fidelity_le_fidelity_channel` — `F(ρ, σ) ≤ F(f ρ, f σ)` for every channel `f` and all states `ρ,
  σ`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Monotonicity of the fidelity under a trace-preserving quantum operation** (Nielsen & Chuang,
Theorem 9.6, `(9.87)`): a quantum channel `f` never decreases the fidelity,
`F(ρ, σ) ≤ F(f ρ, f σ)` for all states `ρ, σ`.
-/
theorem State.fidelity_le_fidelity_channel {f : State S → State S} (hf : IsChannel f)
    (ρ σ : State S) : ρ.fidelity σ ≤ (f ρ).fidelity (f σ) := sorry

end AxQM
