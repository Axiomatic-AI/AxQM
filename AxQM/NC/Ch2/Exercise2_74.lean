/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.Basic.API.Purity
import AxQM.Basic.PartialTrace

/-!
# Nielsen & Chuang, Exercise 2.74 (reduced state of a pure product state)

*(N&C p. 106.)*

For product state |a>|b>, show reduced density operator of A is pure.

* `isPure_reducedLeft_toState_tmul`
-/

namespace AxQM

variable {S T : QSystem}

/-- **Nielsen & Chuang, Exercise 2.74.** The reduced density operator of system `A` alone, for a
composite in the product pure state `|ψ⟩|φ⟩`, is a pure state — namely `|ψ⟩⟨ψ|`. -/
theorem isPure_reducedLeft_toState_tmul (ψ : PureState S) (φ : PureState T) :
    ((ψ ⊗ φ).toState).reducedLeft.IsPure := sorry

end AxQM
