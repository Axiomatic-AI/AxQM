/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ConditionalEntropy
import AxQM.Basic.API.Entropy
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch2.Exercise2_78

/-!
# Nielsen & Chuang, Exercise 11.14 — entanglement and negative conditional entropy

*(N&C p. 514.)*

Show a pure bipartite state |AB> is entangled iff S(B|A)<0.

* `not_isProduct_iff_condVonNeumannEntropy_neg` — the exercise: a bipartite pure state is entangled
  (`¬ IsProduct`) iff its conditional entropy is negative.
-/

noncomputable section

namespace AxQM

namespace PureState

variable {S T : QSystem}

/-- **Nielsen & Chuang, Exercise 11.14.** A pure bipartite state `|AB⟩` is entangled — i.e. *not* a
product state `|a⟩|b⟩` (`¬ ψ.IsProduct`) — if and only if its conditional entropy is negative,
`S(B|A) < 0`. -/
theorem not_isProduct_iff_condVonNeumannEntropy_neg (ψ : PureState (S.compose T)) :
    ¬ ψ.IsProduct ↔ ψ.toState.condVonNeumannEntropy < 0 := sorry

end PureState

end AxQM
