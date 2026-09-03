/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 9.21 (pure-vs-mixed trace distance / fidelity bound)

*(N&C p. 416.)*

Prove 1-F(|psi>,sigma)^2 <= D(|psi>,sigma) for pure vs mixed states.

* `one_sub_fidelity_sq_le_traceDistance`
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.21.** For a pure state `|ψ⟩` and any state `σ`, `1 − F(|ψ⟩, σ)² ≤
D(|ψ⟩, σ)` — a strengthening (for the pure-vs-mixed case) of the general lower bound `1 − F(ρ,
σ) ≤ D(ρ, σ)` of `(9.110)`.
-/
theorem PureState.one_sub_fidelity_sq_le_traceDistance (ψ : PureState S) (σ : State S) :
    1 - (ψ.toState.fidelity σ) ^ 2 ≤ ψ.toState.traceDistance σ := sorry

end AxQM
