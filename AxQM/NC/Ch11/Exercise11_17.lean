/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Purity
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite

/-!
# N&C Exercise 11.17 — an explicit non-trivial mixed `AB` state with `S(A,B) = S(B) − S(A)`

*(N&C p. 516.)*

Find an explicit nontrivial mixed state for AB with S(A,B)=S(B)-S(A).

* `arakiLiebEqualityState` — the witness `|0⟩⟨0| ⊗ I/2` on `qubit ⊗ qubit`.
* `arakiLiebEqualityState_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft` — the saturation
  `S(A,B) = S(B) − S(A)`.
* `arakiLiebEqualityState_not_isPure` — the witness is genuinely mixed.
-/

noncomputable section

namespace AxQM

/-- **The Exercise 11.17 witness** `ρ = |0⟩⟨0|_A ⊗ (I/2)_B` on `qubit ⊗ qubit`: a pure `|0⟩` on the
left factor `A` tensored with the maximally mixed state on the right factor `B`. A non-trivial
(mixed) state saturating the Araki–Lieb triangle inequality `S(A,B) ≥ S(B) − S(A)`. -/
def arakiLiebEqualityState : State (qubit ⊗ qubit) :=
  qubitKet0.toState.tmul (maximallyMixedState qubit)

/-- **The witness saturates the triangle inequality**: `S(A,B) = S(B) − S(A)`. This is the equation
Exercise 11.17 asks for. -/
theorem arakiLiebEqualityState_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft :
    arakiLiebEqualityState.vonNeumannEntropy =
      arakiLiebEqualityState.reducedRight.vonNeumannEntropy -
        arakiLiebEqualityState.reducedLeft.vonNeumannEntropy := sorry

/-- **The witness is genuinely mixed** (non-trivial): `arakiLiebEqualityState` is not a pure
state. -/
theorem arakiLiebEqualityState_not_isPure : ¬ arakiLiebEqualityState.IsPure := sorry

end AxQM
