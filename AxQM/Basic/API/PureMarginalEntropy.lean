/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.Entropy
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# AxQM — equal marginal entropies of a pure bipartite state (`S(A) = S(B)`)

For a pure state `ψ` of a composite system `A ⊗ B`, the two reduced states have equal von Neumann
entropy: `S(A) = S(B)`. This is Nielsen & Chuang **Theorem 11.8, part (3)** (eq. (11.88)).

## Main result

* `AxQM.PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight` — `S(A) = S(B)` for a pure
  bipartite state.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The reduced states of a pure composite are isentropic** (Nielsen–Chuang Theorem 11.8, part
(3)). -/
theorem PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight {T : QSystem}
    (ψ : PureState (S.compose T)) :
    ψ.toState.reducedLeft.vonNeumannEntropy = ψ.toState.reducedRight.vonNeumannEntropy := sorry

end AxQM
