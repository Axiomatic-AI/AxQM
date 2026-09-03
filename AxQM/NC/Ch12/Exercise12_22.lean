/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.CoherentInformation
import AxQM.NC.Ch12.Exercise12_15
import AxQM.NC.Ch2.Exercise2_78
import AxQM.NC.Ch2.Exercise2_80
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Evolution
import AxQM.Basic.SystemIso
import AxQM.Basic.API.Associator
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.Interchange
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProductInterchange
import AxQM.Basic.API.SameNonzeroSpectrum
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.PartialTrace
import AxQM.Basic.API.LeftPairGate

/-!
# N&C Exercise 12.22 — Entanglement conversion without communication (the model)

*(N&C p. 577.)*

Entanglement conversion without communication possible iff lambda_psi ~= lambda_phi tensor x.

* `dilatedChannelOnLeft` — Alice's dilated quantum operation on the left factor.
* `dilatedChannelNoComm` — the two-sided no-communication channel (Bob's dilation on the right
  factor followed by Alice's on the left).
* `ConvertibleNoComm` — convertibility of one bipartite pure state into another by local operations
  with no classical communication.
* `convertibleNoComm_iff_exists_sameNonzeroSpectrum_tmul` — the biconditional of the exercise.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Alice's dilated quantum operation on the left factor `A`.** For a bipartite state `ρ` on `A ⊗
B`, a unitary `U` on `A ⊗ C`, and an ancilla `C` prepared in the pure state `ω`, this is the
state on `A ⊗ B` obtained by applying Nielsen & Chuang's Chapter-8 dilation of a channel `E` on
`A` to the left factor. It is defined
by conjugating `dilatedChannelOnRight` with the swap `A ⊗ B ≃ B ⊗ A` (`QSystem.Iso.comm`): swap
the two factors, dilate the channel on the (now right-hand) `A` factor, then swap back. -/
noncomputable def State.dilatedChannelOnLeft (ρ : State (A ⊗ B)) (U : Evolution (A ⊗ C))
    (ω : PureState C) : State (A ⊗ B) :=
  State.congr (QSystem.Iso.comm B A)
    ((State.congr (QSystem.Iso.comm A B) ρ).dilatedChannelOnRight U ω)

variable {CA CB : QSystem}

/-- **The two-sided no-communication dilated channel.** For a bipartite state `ρ` on `A ⊗ B`,
Alice's dilation `(UA, ωA)` on `A ⊗ CA` and Bob's dilation `(UB, ωB)` on `B ⊗ CB`, this is the
state on `A ⊗ B` obtained by running Bob's local dilated channel on the right factor and *then*
Alice's on the left factor — the two parties acting independently, with no operation conditioned
on the other's (the "no communication" constraint). -/
noncomputable def State.dilatedChannelNoComm (ρ : State (A ⊗ B)) (UA : Evolution (A ⊗ CA))
    (UB : Evolution (B ⊗ CB)) (ωA : PureState CA) (ωB : PureState CB) : State (A ⊗ B) :=
  (ρ.dilatedChannelOnRight UB ωB).dilatedChannelOnLeft UA ωA

universe uCA uCB

/-- **Entanglement conversion without classical communication.** `ψ.ConvertibleNoComm φ` holds when
Alice and Bob can convert the bipartite pure state `|ψ⟩` on `A ⊗ B` into `|φ⟩` using local
operations only — no classical communication (Nielsen & Chuang, Exercise 12.22). Each party's
local operation is modelled by its Stinespring / Chapter-8 dilation. The two dilations act on
disjoint factors, capturing "no communication": neither operation is conditioned on the other's
result.

The ancilla systems `CA`, `CB` are quantified over their own universes (`QSystem.{uCA}`,
`QSystem.{uCB}`).
-/
def PureState.ConvertibleNoComm {A B : QSystem} (ψ φ : PureState (A ⊗ B)) : Prop :=
  ∃ (CA : QSystem.{uCA}) (CB : QSystem.{uCB}) (UA : Evolution (A ⊗ CA)) (UB : Evolution (B ⊗ CB))
    (ωA : PureState CA) (ωB : PureState CB),
    φ.toState = ψ.toState.dilatedChannelNoComm UA UB ωA ωB

/-- **Nielsen & Chuang Exercise 12.22 (the biconditional).** Alice and Bob can convert the bipartite
pure state `|ψ⟩` on `A ⊗ B` into `|φ⟩` by local operations with **no** classical communication
if and only if the Schmidt-coefficient vector of `ψ` equals that of `φ` tensored with a
probability vector.

The ancilla systems are taken in universe `0`.
-/
theorem PureState.convertibleNoComm_iff_exists_sameNonzeroSpectrum_tmul.{uA, uB}
    {A : QSystem.{uA}} {B : QSystem.{uB}} (ψ φ : PureState (A ⊗ B)) :
    PureState.ConvertibleNoComm.{0, 0, uA, uB} ψ φ ↔
      ∃ (C : QSystem.{0}) (τ : State C),
        ψ.toState.reducedLeft.SameNonzeroSpectrum (φ.toState.reducedLeft.tmul τ) := sorry

end AxQM
