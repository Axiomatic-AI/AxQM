/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Exercise11_24
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.Associator
import AxQM.Basic.API.Entropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.Basic.API.MutualInformation

/-!
# N&C Theorem 11.16 — subadditivity of the conditional entropy

*(N&C p. 523.)*

Subadditivity of the conditional entropy in first and second entries.

* `vonNeumannEntropy_cond_subadditive_first` — (11.117) first entry —
  `State.vonNeumannEntropy_cond_subadditive_first`, for a three-system composite, `S(A,B|C) ≤ S(A|C)
  + S(B|C)`;
* `vonNeumannEntropy_joint_cond_subadditive` — (11.116) joint —
  `State.vonNeumannEntropy_joint_cond_subadditive`, four-system composite, `S(A,B|C,D) ≤ S(A|C) +
  S(B|D)`;
* `vonNeumannEntropy_cond_subadditive_second` — (11.118) second entry —
  `State.vonNeumannEntropy_cond_subadditive_second`, `S(A|B,C) ≤ S(A|B) + S(A|C)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C D : QSystem}

/-- **N&C Theorem 11.16, subadditivity of the conditional entropy in the first entry (11.117).** For
an **arbitrary** state `ρ` on the tripartite system `A ⊗ (C ⊗ B)`,

`S(A,B|C) ≤ S(A|C) + S(B|C)`.
-/
theorem State.vonNeumannEntropy_cond_subadditive_first (ρ : State (A ⊗ (C ⊗ B))) :
    ρ.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy ≤
      ((ρ.congr (QSystem.assoc A C B)).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedLeft.vonNeumannEntropy)
        + (ρ.reducedRight.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy) := sorry

/-- **N&C Theorem 11.16, joint subadditivity of the conditional entropy (11.116).** For an
**arbitrary** state `ρ` on the four-system composite `A ⊗ (C ⊗ (D ⊗ B))`,

`S(A,B|C,D) ≤ S(A|C) + S(B|D)`,

with each conditional entropy written as its defining difference. The marginals are read off as
reduced states: `S(A,B,C,D) = S(ρ)`; `S(C,D) = S((ρ.reducedRight.congr (assoc C D
B)).reducedLeft)` (the `C ⊗ D` marginal of the `B,C,D` marginal `ρ.reducedRight`); `S(A,C) =
S((ρ.congr (assoc A C (D ⊗ B))).reducedLeft)` (trace out `D ⊗ B`); `S(C) =
S(ρ.reducedRight.reducedLeft)`; `S(B,D) = S(ρ.reducedRight.reducedRight)`; `S(D) =
S(ρ.reducedRight.reducedRight.reducedLeft)`. So `S(A,B|C,D) = S(ρ) − S(C,D)`, `S(A|C) = S(A,C) −
S(C)`, `S(B|D) = S(B,D) − S(D)`.
-/
theorem State.vonNeumannEntropy_joint_cond_subadditive (ρ : State (A ⊗ (C ⊗ (D ⊗ B)))) :
    ρ.vonNeumannEntropy
        - (ρ.reducedRight.congr (QSystem.assoc C D B)).reducedLeft.vonNeumannEntropy ≤
      ((ρ.congr (QSystem.assoc A C (D ⊗ B))).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedLeft.vonNeumannEntropy)
        + (ρ.reducedRight.reducedRight.vonNeumannEntropy
          - ρ.reducedRight.reducedRight.reducedLeft.vonNeumannEntropy) := sorry

/-- **N&C Theorem 11.16, subadditivity of the conditional entropy in the second entry (11.118).**
For an **arbitrary** state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A|B,C) ≤ S(A|B) + S(A|C)`,

with each conditional entropy written as its defining difference — `S(A|B,C) = S(ρ) − S(B,C)`,
`S(A|B) = S(A,B) − S(B)`, `S(A|C) = S(A,C) − S(C)` — and the marginals read off as reduced
states.

Equivalent to N&C (11.123), `S(A,B,C) + S(B) + S(C) ≤ S(A,B) + S(A,C) + S(B,C)`.
-/
theorem State.vonNeumannEntropy_cond_subadditive_second (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy ≤
      ((ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedLeft.vonNeumannEntropy)
        + (((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
              (QSystem.assoc A C B)).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedRight.vonNeumannEntropy) := sorry

end AxQM
