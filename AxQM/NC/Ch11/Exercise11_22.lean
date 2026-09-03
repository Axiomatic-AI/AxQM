/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyMixLine
import AxQM.Basic.API.MaximallyMixed

/-!
# N&C Exercise 11.22 — alternate (second-derivative) proof of concavity of the entropy

*(N&C p. 518.)*

Alternate proof of concavity: show f(p)=S(p rho+(1-p)sigma) has f''(p)<=0.

* `vonNeumannEntropy_concave` — the two-point concavity inequality (11.79) for arbitrary states.
-/

open scoped ComplexOrder

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang Exercise 11.22 — concavity of the von Neumann entropy, for all states.** The
two-point concavity inequality (Nielsen & Chuang eq. (11.79) for two components): for arbitrary
states `ρ, σ` and `0 ≤ p ≤ 1`,

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`.

This is the culmination of the exercise's alternate (second-derivative) proof.
-/
theorem State.vonNeumannEntropy_concave {ρ σ : State S} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy
      ≤ (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy := sorry

end AxQM
