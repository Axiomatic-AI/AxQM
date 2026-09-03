/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.PartialTrace

/-!
# AxQM — quantum conditional entropy `S(A|B)`

The **quantum conditional entropy** of a bipartite state `ρ` on `A ⊗ B` (Nielsen & Chuang §11.3.4,
summary of Chapter 11) is `S(A|B) = S(A,B) − S(B)`.

## Main definitions

* `AxQM.State.condVonNeumannEntropy` — `S(A|B) = S(A,B) − S(B)`.
-/

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **quantum conditional entropy** `S(A|B) = S(A,B) − S(B)` of a bipartite state `ρ` on
`A ⊗ B`. Nielsen & Chuang §11.3.4. May be negative when `A` and `B` are entangled. -/
def State.condVonNeumannEntropy (ρ : State (S ⊗ T)) : ℝ :=
  ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy

/-- The **coherent information** `I(A⟩B) = S(B) − S(A,B)` of a bipartite state `ρ` on `A ⊗ B`, the
negative of the conditional entropy `S(A|B)` (Nielsen & Chuang §12.4.2). It measures how much
quantum information about the reference `A` is preserved by the state on `B`; being `−S(A|B)`,
it is positive exactly when `S(A|B) < 0`, i.e. when `A` and `B` are entangled. -/
def State.coherentInfoOfState (ρ : State (S ⊗ T)) : ℝ := -ρ.condVonNeumannEntropy

end AxQM
