/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ControlledPowerSequence
import AxQM.Concrete.BitStringValue

/-!
# Nielsen & Chuang, Exercise 5.7 — the phase-estimation controlled-`U` sequence

*(N&C p. 222.)*

Show the controlled-U sequence takes |j>|u> to |j>U^j|u>, not depending on |u> being eigenstate.

* `seqCtrlPow_evolvePure` — `seqCtrlPow U t` takes `|j⟩|u⟩` to `|j⟩ Uʲ|u⟩`, where
  `j = bitsToNat t b`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 5.7.** The sequence of controlled-`U` operations of Figure 5.2
takes `|j⟩|u⟩` to `|j⟩ Uʲ|u⟩`, with no hypothesis that `u` is an eigenstate of `U`. -/
theorem seqCtrlPow_evolvePure (U : Evolution S) :
    ∀ (t : ℕ) (b : Fin t → Fin 2) (u : PureState S),
      (seqCtrlPow U t).evolvePure (qtowerKet t b u)
        = qtowerKet t b ((U ^ Concrete.bitsToNat t b).evolvePure u)
  := sorry

end AxQM
