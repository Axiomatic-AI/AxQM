/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.Associator
import AxQM.Basic.API.Entropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.Basic.API.MutualInformation
import AxQM.NC.Ch11.StrongSubadditivityGeneral

/-!
# N&C Exercise 11.24 — weak monotonicity from strong subadditivity

*(N&C p. 521.)*

Show S(A)+S(B)<=S(A,C)+S(B,C) can be obtained as a consequence of strong subadditivity.

* `vonNeumannEntropy_weakMonotonicity`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Weak monotonicity of the von Neumann entropy** (Nielsen & Chuang, Exercise 11.24, the "form-1"
strong-subadditivity inequality eq. (11.107)): for an arbitrary state `ρ` on the tripartite
system `A ⊗ (B ⊗ C)`,

`S(A) + S(C) ≤ S(A,B) + S(B,C)`.
-/
theorem State.vonNeumannEntropy_weakMonotonicity (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.reducedLeft.vonNeumannEntropy + ρ.reducedRight.reducedRight.vonNeumannEntropy ≤
      (State.congr (QSystem.assoc A B C) ρ).reducedLeft.vonNeumannEntropy
        + ρ.reducedRight.vonNeumannEntropy := sorry

end AxQM
