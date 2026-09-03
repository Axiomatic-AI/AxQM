/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Associator
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.ReferencePurification
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Support
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.Core.ConditionalEntropy
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Theorem11_15
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch12.Problem12_1
import AxQM.NC.Ch2.Exercise2_78
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState

/-!
# Entropy exchange and coherent information (N&C §12.4.1–12.4.2)

* `entropyExchange`
* `coherentInfo`
* `coherentInfo_le_vonNeumannEntropy`
* `coherentInfoComp`
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {A B C Q : QSystem}

/-- **Entropy exchange** `S(ρ, E)` of a quantum operation `E` on `Q`, presented by its dilation `(U,
ω)` (Nielsen & Chuang §12.4.1, eq. (12.107)). Equivalently this is `S(W)` for the
w-matrix `W_{ij} = tr(Eᵢ ρ Eⱼ†)`; the purification form is used here because the data processing
inequality argument reasons about the `R'Q'` bipartition directly. -/
def State.entropyExchange (ρ : State Q) (U : Evolution (Q ⊗ C)) (ω : PureState C) : ℝ :=
  ((State.refPurify ρ).toState.dilatedChannelOnRight U ω).vonNeumannEntropy

/-- **Coherent information** `I(ρ, E)` of a quantum operation `E` on `Q`, presented by its dilation
`(U, ω)` (Nielsen & Chuang §12.4.2, eq. (12.118)):

`I(ρ, E) = S(E(ρ)) − S(ρ, E)`,

the entropy of the output state `E(ρ) = ρ.dilatedChannel U ω` minus the entropy exchange
`State.entropyExchange`. It plays, in the quantum data processing inequality (Theorem 12.10), the
role the mutual information `H(X:Y)` plays classically. -/
def State.coherentInfo (ρ : State Q) (U : Evolution (Q ⊗ C)) (ω : PureState C) : ℝ :=
  (ρ.dilatedChannel U ω).vonNeumannEntropy - ρ.entropyExchange U ω

/-- **First inequality of the quantum data processing inequality** (Nielsen & Chuang Theorem 12.10,
eq. (12.119), first stage): the coherent information never exceeds the input entropy,

`I(ρ, E) ≤ S(ρ)`.

This is N&C's argument (12.122)–(12.126) cast in the purification picture. N&C note equality
holds iff `E` is perfectly reversible on `ρ`.
-/
theorem State.coherentInfo_le_vonNeumannEntropy (ρ : State Q) (U : Evolution (Q ⊗ C))
    (ω : PureState C) : ρ.coherentInfo U ω ≤ ρ.vonNeumannEntropy := sorry

/-- **Coherent information of the two-stage composed operation** `I(ρ, E2 ∘ E1)` (Nielsen & Chuang
Theorem 12.10). The composed coherent information is the state coherent information of `R''Q''`:

`I(ρ, E2 ∘ E1) = I(R''⟩Q'') = S((E2 ∘ E1)(ρ)) − S(ρ, E2 ∘ E1)`.

Presenting the composition as sequential right-factor dilations, rather than as one dilation on
a combined environment `Q ⊗ (C₁ ⊗ C₂)`, avoids reshaping across the joint environment while
remaining faithful to N&C.
-/
def State.coherentInfoComp (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : ℝ :=
  (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂
    ω₂).coherentInfoOfState

end AxQM
