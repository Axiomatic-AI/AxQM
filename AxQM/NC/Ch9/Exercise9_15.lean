/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_4
import AxQM.NC.Ch2.Exercise2_81
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.PureState
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# Nielsen & Chuang, Exercise 9.15 (Uhlmann's theorem with one purification fixed)

*(N&C p. 411.)*

Show F(rho,sigma)=max over purifications of sigma with psi fixed purification of rho.

* `isGreatest_norm_overlap_purification_fixed` — Exercise 9.15, `(9.72)`: `F(ρ, σ) = max_{|φ⟩}
  ‖⟨ψ|φ⟩‖` over purifications `φ` of `σ`, for any fixed purification `ψ` of `ρ`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.15**, `(9.72)`: for any **fixed** purification `ψ` of `ρ` into
the doubled system `S ⊗ S`, the fidelity `F(ρ, σ)` is the **greatest overlap magnitude**
`‖⟨ψ|φ⟩‖` achievable over all purifications `φ` of `σ`: `F(ρ, σ) = max_{|φ⟩} |⟨ψ|φ⟩|`.

Only `φ` varies, the purification of `ρ` being fixed, yet the maximum is `F(ρ, σ)` whatever
purification `ψ` of `ρ` was chosen. Packaged as `IsGreatest`: `ρ.fidelity σ` is attained by some
purification `φ` of `σ` and upper-bounds every achievable overlap.
-/
theorem State.isGreatest_norm_overlap_purification_fixed (ρ σ : State S)
    (ψ : PureState (S ⊗ S)) (hψ : ψ.toState.reducedLeft = ρ) :
    IsGreatest
      {r : ℝ | ∃ φ : PureState (S ⊗ S),
        φ.toState.reducedLeft = σ ∧ r = ‖ψ.overlap φ‖}
      (ρ.fidelity σ) := sorry

end AxQM
