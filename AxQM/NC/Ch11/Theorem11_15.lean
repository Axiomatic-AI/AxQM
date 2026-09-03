/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.Basic.API.Associator
import AxQM.Basic.API.Entropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.PartialTrace
import AxQM.Basic.API.Evolution

/-!
# N&C Theorem 11.15 — reformulations of strong subadditivity

*(N&C p. 522.)*

Reformulations of strong subadditivity: conditioning reduces entropy; discarding/operations never
increase mutual info.

* `conditioning_reduces_vonNeumannEntropy'` — N&C Thm 11.15(1), arbitrary `ρ`.
* `vonNeumannMutualInfo_le_of_discard'` — N&C Thm 11.15(2), arbitrary `ρ`.
* `dilatedChannelOnRight` — the output `(id_A ⊗ E) ρ` of a dilated channel on `B`.
* `vonNeumannMutualInfo_dilatedChannelOnRight_le` — N&C Thm 11.15(3).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **N&C Theorem 11.15(1), faithful form: conditioning reduces entropy for every state.** For an
*arbitrary* state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A|B,C) ≤ S(A|B)`.
-/
theorem State.conditioning_reduces_vonNeumannEntropy' (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy ≤
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy -
        ρ.reducedRight.reducedLeft.vonNeumannEntropy := sorry

/-- **N&C Theorem 11.15(2), faithful form: discarding never increases mutual information for every
state.** For an *arbitrary* state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A:B) ≤ S(A:B,C)`.

Every state's operator is a density operator, so no faithfulness hypothesis is needed — matching
N&C, who state the reformulation for a general quantum state.
-/
theorem State.vonNeumannMutualInfo_le_of_discard' (ρ : State (A ⊗ (B ⊗ C))) :
    ((ρ.congr (QSystem.assoc A B C)).reducedLeft).vonNeumannMutualInfo ≤
      ρ.vonNeumannMutualInfo := sorry

/-- **The output of a dilated quantum operation on `B`.** For a bipartite state `ρ` on `A ⊗ B`, a
unitary `U` on `B ⊗ C`, and an ancilla `C` prepared in the pure state `ω`, this is the state on
`A ⊗ B` obtained by Nielsen & Chuang's Chapter-8 dilation of a channel `E` on `B`: adjoin the
pure ancilla (`ρ ⊗ |ω⟩⟨ω|`, re-associated to `A ⊗ (B ⊗ C)`), let `U` act on the `B ⊗ C` factor
(`I_A ⊗ U`), then discard `C` (re-associate to `(A ⊗ B) ⊗ C` and trace it out). -/
noncomputable def State.dilatedChannelOnRight (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : State (A ⊗ B) :=
  ((((Evolution.id (S := A)).tmul U).evolve
      (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState))).congr
      (QSystem.assoc A B C)).reducedLeft

/-- **N&C Theorem 11.15(3): quantum operations never increase mutual information.** For a bipartite
state `ρ` on `A ⊗ B` and a trace-preserving quantum operation `E` on `B`, presented by its
Chapter-8 dilation (a unitary `U` on `B ⊗ C` with the ancilla `C` in a pure state `ω`),

`S(A' : B') ≤ S(A : B)`,

where the primed state is `(id_A ⊗ E) ρ = ρ.dilatedChannelOnRight U ω`.

Stating the operation via its dilation is faithful to N&C's own argument.
-/
theorem State.vonNeumannMutualInfo_dilatedChannelOnRight_le (ρ : State (A ⊗ B))
    (U : Evolution (B ⊗ C)) (ω : PureState C) :
    (ρ.dilatedChannelOnRight U ω).vonNeumannMutualInfo ≤ ρ.vonNeumannMutualInfo := sorry

end AxQM
