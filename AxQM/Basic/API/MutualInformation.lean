/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Entropy
import AxQM.Basic.PartialTrace

/-!
# AxQM — quantum mutual information `S(A:B)`

The **quantum mutual information** of a bipartite state `ρ` on `A ⊗ B` (Nielsen & Chuang §11.3.4,
eq. (11.60)).

## Main definitions

* `AxQM.State.vonNeumannMutualInfo` — `S(A:B) = S(A) + S(B) − S(A,B)`.
-/

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **quantum mutual information** `S(A:B) = S(A) + S(B) − S(A,B)` of a bipartite state `ρ` on
`A ⊗ B`. Nielsen & Chuang §11.3.4, eq. (11.60). -/
def State.vonNeumannMutualInfo (ρ : State (S ⊗ T)) : ℝ :=
  ρ.reducedLeft.vonNeumannEntropy + ρ.reducedRight.vonNeumannEntropy - ρ.vonNeumannEntropy

end AxQM
