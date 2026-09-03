/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch2.Exercise2_75
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.EntropyComposite
import AxQM.NC.Ch11.Exercise11_24

/-!
# N&C Exercise 11.26 — `S(A:B) + S(A:C) ≤ 2 S(A)`, and an example where `S(A:B) > S(A)`

*(N&C p. 522.)*

Prove S(A:B)+S(A:C)<=2S(A); find an example where S(A:B)>S(A).

* `exists_vonNeumannMutualInfo_gt_reducedLeft_vonNeumannEntropy` — the existence statement realising
  "find an example where `S(A:B) > S(A)`".
* `vonNeumannMutualInfo_add_le_two_mul_vonNeumannEntropy` — the bound `S(A:B) + S(A:C) ≤ 2 S(A)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable (x y : Fin 2)

/-- **N&C Exercise 11.26 (the example).** There is a bipartite state `ρ` on some `A ⊗ B` whose
quantum mutual information strictly exceeds the marginal entropy of the first system,
`S(A) < S(A:B)` — witnessing that the classical bound `H(A:B) ≤ H(A)` fails in the quantum
setting. -/
theorem exists_vonNeumannMutualInfo_gt_reducedLeft_vonNeumannEntropy :
    ∃ (A B : QSystem.{0}) (ρ : State (A ⊗ B)),
      ρ.reducedLeft.vonNeumannEntropy < ρ.vonNeumannMutualInfo := sorry

/-! ### Part (1): the bound `S(A:B) + S(A:C) ≤ 2 S(A)` -/

variable {A B C : QSystem}

/-- **N&C Exercise 11.26 (the bound).** For a tripartite state `ρ` on `A ⊗ (B ⊗ C)`, the two
pairwise quantum mutual informations obey

`S(A:B) + S(A:C) ≤ 2 S(A)`  (N&C eq. (11.114)),

where `S(A:B)` is the mutual information of the `A ⊗ B` marginal `(ρ.congr (assoc A B
C)).reducedLeft` and `S(A:C)` that of the `A ⊗ C` marginal `((ρ.congr (id ⊗ comm B C)).congr
(assoc A C B)).reducedLeft`. The *per-term* Shannon bound `H(A:B) ≤ H(A)` has no quantum analogue,
yet the *sum* still obeys `≤ 2 S(A)`.
-/
theorem State.vonNeumannMutualInfo_add_le_two_mul_vonNeumannEntropy (ρ : State (A ⊗ (B ⊗ C))) :
    (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannMutualInfo
        + ((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
            (QSystem.assoc A C B)).reducedLeft.vonNeumannMutualInfo
      ≤ 2 * ρ.reducedLeft.vonNeumannEntropy := sorry

end AxQM
