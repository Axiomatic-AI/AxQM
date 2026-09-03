/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.AmplitudeDampingChannel
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance
import AxQM.Basic.API.HSOverlap
import AxQM.Basic.API.BlochState
import AxQM.Concrete.BlochMatrix
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 10.13 (Minimum fidelity of the amplitude-damping channel)

*(N&C p. 443.)*

Min fidelity F(|psi>,E(|psi><psi|)) for amplitude damping channel parameter gamma is sqrt(1-gamma).

* `amplitudeDampingChannel_isLeast_fidelity`
-/

open Matrix

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.13.** `√(1 − γ)` is the **minimum** fidelity of the
amplitude-damping channel over pure input states: it is the `IsLeast` of the set of per-state
fidelities `{F | ∃ ψ, F(|ψ⟩, E(|ψ⟩⟨ψ|)) = F}`. -/
theorem amplitudeDampingChannel_isLeast_fidelity (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsLeast {F : ℝ | ∃ ψ : PureState qubit,
        ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState) = F}
      (Real.sqrt (1 - γ)) := sorry

end AxQM
