/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.AugmentedSearchOracle

/-!
# Nielsen & Chuang, Exercise 6.5 (the augmented oracle `O'` from one call to `O`)

*(N&C p. 255.)*

Show the augmented oracle O' can be built from one call to O and elementary gates using extra qubit.

* `augmentedSearchOracle_marks_solution_and_zero`
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.5 — the augmented oracle `O'` from one call to `O`.** For **any**
one-call bit-flip oracle `O` for `f : Fin N → Fin 2` on the augmented register
`qudit N ⊗ (qubit ⊗ qubit)` (search index `|x⟩`, extra qubit `|q⟩`, response `|r⟩`), the augmented
circuit
`augmentedSearchOracle O` — built from **one** application of `O` and the elementary gates
`X_r`, `CNOT_{q→r}`, `H_r` on the extra qubit `|q⟩` — implements the augmented oracle `O'`: on
the response work qubit supplied in `|0⟩`, `|x⟩|q⟩|0⟩` is an eigenstate whose eigenvalue is `−1`
exactly when the item is a solution (`f(x) = 1`) **and** the extra bit is `q = 0`, and `+1`
otherwise. That is `O'` marks `(x, q)` iff `x` is a solution and `q = 0`, for every item `x` of
the search space, with the work qubit returned to `|0⟩`.
-/
theorem augmentedSearchOracle_marks_solution_and_zero {N : ℕ} {f : Fin N → Fin 2}
    {O : Evolution ((qudit N).compose (qubit.compose qubit))} (h : IsSearchBitFlipOracle f O)
    (x : Fin N) (q : Fin 2) :
    (augmentedSearchOracle O).HasEigenstate (if f x = 1 ∧ q = 0 then -1 else 1)
      ((quditBasis x).tmul ((qubitBasis q).tmul (qubitBasis 0))) := sorry

end AxQM
