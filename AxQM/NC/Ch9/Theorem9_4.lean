/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PureState
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite
import AxQM.Basic.API.Fidelity
import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-!
# Nielsen & Chuang, Theorem 9.4 (Uhlmann's theorem)

*(N&C p. 410.)*

Uhlmann's theorem: F(rho,sigma)=max over purifications |<psi|phi>|.

* `isGreatest_norm_overlap_purification` — Uhlmann's theorem, `(9.62)`: `F(ρ, σ) = max ‖⟨ψ|φ⟩‖` over
  purifications `ψ` of `ρ`, `φ` of `σ` into `S ⊗ S`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Theorem 9.4 (Uhlmann's theorem)**, `(9.62)`: the fidelity `F(ρ, σ)` is the
**greatest overlap magnitude** `‖⟨ψ|φ⟩‖` achievable over all purifications `ψ` of `ρ` and `φ` of
`σ` into the doubled system `S ⊗ S` (the ancilla a copy of the system): `F(ρ, σ) = max_{|ψ⟩,|φ⟩}
|⟨ψ|φ⟩|`.

Packaged as `IsGreatest`: `ρ.fidelity σ` both lies in the achievable set (attained by the
optimal pair of purifications) and upper-bounds it.
-/
theorem State.isGreatest_norm_overlap_purification (ρ σ : State S) :
    IsGreatest
      {r : ℝ | ∃ ψ φ : PureState (S ⊗ S),
        ψ.toState.reducedLeft = ρ ∧ φ.toState.reducedLeft = σ ∧
        r = ‖ψ.overlap φ‖}
      (ρ.fidelity σ) := sorry

end AxQM
