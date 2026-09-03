/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SixStateProtocol
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.29 — the six-state protocol

*(N&C p. 591.)*

Give six-state protocol; argue security; discuss noise/eavesdropping sensitivity.

* `sixStateState_hasEigenstate`
* `sixState_bornProb_matchedBasis`
* `sixState_bornProb_mismatchedBasis_uncorrelated`
-/

noncomputable section

namespace AxQM

/-- **Each of the six states is the `(-1)^s`-eigenstate of its basis observable.** For the `X` basis
`X|+⟩ = |+⟩`, `X|−⟩ = −|−⟩`; for `Y`, `Y|+i⟩ = |+i⟩`, `Y|−i⟩ = −|−i⟩`; for `Z`, `Z|0⟩ = |0⟩`,
`Z|1⟩ = −|1⟩` — the Pauli-eigenstate content of N&C Exercise 4.1 (`qubit{Plus,Minus,PlusI,MinusI,
Ket0}_hasEigenstate_pauli*`, `qubitBasis_one_hasEigenstate_pauliZ`). This certifies that the six
protocol states really are the eigenstates of `X`, `Y`, and `Z`. -/
theorem sixStateState_hasEigenstate (i : Fin 3) (s : Fin 2) :
    (sixStateObservable i).HasEigenstate (signEigenvalue s) (sixStateState i s) := sorry

/-- **Matched bases: Bob recovers Alice's bit with certainty.** When Bob measures in the same basis
Alice prepared (`j = i`), his outcome equals Alice's data bit `s` with probability one:
`p(outcome = s) = 1`. Because `sixStateState i s` is the `(-1)^s`-eigenstate of `sixStateObservable
i`, the outcome is deterministic. This is the correctness of the sifted key. -/
theorem sixState_bornProb_matchedBasis (i : Fin 3) (s : Fin 2) :
    (sixStateMeasurement i).bornProb (sixStateState i s).toState s = 1 := sorry

/-- **Mismatched bases: Bob's result is uncorrelated with Alice's bit.** When Bob measures in the
wrong basis, the distribution of his outcome is independent of Alice's data bit `s`: for any two
bits `s₁, s₂` and any outcome `o`, the probabilities agree. Both equal `1/2`, so a wrong-basis
measurement carries no information about Alice's bit — the six-state analogue of BB84's
"completely uncorrelated". -/
theorem sixState_bornProb_mismatchedBasis_uncorrelated (i j : Fin 3) (s₁ s₂ o : Fin 2)
    (h : i ≠ j) :
    (sixStateMeasurement j).bornProb (sixStateState i s₁).toState o
      = (sixStateMeasurement j).bornProb (sixStateState i s₂).toState o := sorry

end AxQM
