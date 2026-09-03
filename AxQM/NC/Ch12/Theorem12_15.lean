/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.StateMajorization

/-!
# Nielsen–Chuang, Theorem 12.15 — Nielsen's theorem

*(N&C p. 576.)*

Bipartite pure |psi> -> |phi> by LOCC iff lambda_psi prec lambda_phi.

* `loccConvertible_iff_majorize`
-/

namespace AxQM

namespace State

variable {S : QSystem}

/-- **Nielsen's theorem** (Nielsen–Chuang, Theorem 12.15), reduced-state form: a bipartite pure
state `|ψ⟩` can be converted to `|ϕ⟩` by one-way LOCC iff the reduced state `ρ = ρ_ψ` is
majorized by `σ = ρ_ϕ` (`λ_ψ ≺ λ_ϕ`). -/
theorem loccConvertible_iff_majorize {ρ σ : State S} :
    ρ.LOCCConvertible σ ↔ ρ.Majorize σ := sorry

end State

end AxQM
