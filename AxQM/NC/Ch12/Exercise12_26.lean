/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BB84
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.26 — BB84 measurement outcomes

*(N&C p. 588.)*

BB84: when b'_k != b_k, a'_k random & uncorrelated with a_k; when equal, a'_k=a_k.

* `bb84_bornProb_matchedBasis` — Matched bases (`b′ = b`): `|ψ_{ab}⟩` is the `(-1)^a`-eigenstate of
  the measured observable, so the outcome is *deterministic* and equals `a` —
  `bb84_bornProb_matchedBasis` (`p(a′ = a) = 1`).
* `bb84_bornProb_mismatchedBasis`
* `bb84_bornProb_mismatchedBasis_uncorrelated`
-/

noncomputable section

namespace AxQM

/-- **Matched bases: Bob recovers Alice's bit with certainty, `a′ = a`.** When Bob measures in the
same basis Alice prepared (`b′ = b`), the outcome equals Alice's data bit `a` with probability one:
`p(a′ = a) = 1`. This is N&C's "when `b′_k = b_k`, `a′_k = a_k`". -/
theorem bb84_bornProb_matchedBasis (a b : Fin 2) :
    (bb84Measurement b).bornProb (bb84State a b).toState a = 1 := sorry

/-- **Mismatched bases: Bob's result is random, `p(a′ = j) = 1/2`.** When Bob measures in the wrong
basis (`b′ ≠ b`), each outcome `j ∈ {0, 1}` occurs with probability exactly `1/2`. This is N&C's
"when `b′_k ≠ b_k`, `a′_k` is random". -/
theorem bb84_bornProb_mismatchedBasis (a b b' j : Fin 2) (h : b ≠ b') :
    (bb84Measurement b').bornProb (bb84State a b).toState j = 1 / 2 := sorry

/-- **Mismatched bases: `a′_k` is completely uncorrelated with `a_k`.** When Bob measures in the
wrong basis, the distribution of his result bit `a′` is independent of Alice's data bit `a`: for
any two data bits `a₁, a₂` and any outcome `j`, the probabilities agree. -/
theorem bb84_bornProb_mismatchedBasis_uncorrelated (a₁ a₂ b b' j : Fin 2) (h : b ≠ b') :
    (bb84Measurement b').bornProb (bb84State a₁ b).toState j
      = (bb84Measurement b').bornProb (bb84State a₂ b).toState j := sorry

end AxQM
