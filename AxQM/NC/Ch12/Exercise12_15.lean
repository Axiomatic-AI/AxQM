/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.CoherentInformation
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# N&C Exercise 12.15 — entropy inequalities for a two-stage quantum process

*(N&C p. 568.)*

Derive all subadditivity/strong-subadditivity inequalities for two-stage process.

* `entropyExchange_le_vonNeumannEntropy_add_dilatedChannel` —
  `State.entropyExchange_le_vonNeumannEntropy_add_dilatedChannel` : `S(ρ, E) ≤ S(ρ) + S(E(ρ))`
  (subadditivity on `R'Q'`);
* `vonNeumannEntropy_le_dilatedChannel_add_entropyExchange` —
  `State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange` : `S(ρ) ≤ S(E(ρ)) + S(ρ, E)`, i.e.
  N&C eq. (12.144) `ΔS + S(ρ, E) ≥ 0` — the "second law" inequality highlighted just before the
  exercise (triangle on `R'Q'`);
* `dilatedChannelComp` — the composite entropy exchange `S(ρ, E₂∘E₁) = S(R''Q'')`, and
  `State.dilatedChannelComp` — the composite output `ρ'' = (E₂∘E₁)(ρ)`;
* `entropyExchangeComp` — the composite entropy exchange `S(ρ, E₂∘E₁) = S(R''Q'')`, and
  `State.dilatedChannelComp` — the composite output `ρ'' = (E₂∘E₁)(ρ)`;
* `entropyExchangeComp_le_vonNeumannEntropy_add_dilatedChannelComp` —
  `State.entropyExchangeComp_le_vonNeumannEntropy_add_dilatedChannelComp` : `S(ρ, E₂∘E₁) ≤ S(ρ) +
  S(ρ'')`;
* `vonNeumannEntropy_le_dilatedChannelComp_add_entropyExchangeComp` —
  `State.vonNeumannEntropy_le_dilatedChannelComp_add_entropyExchangeComp` : `S(ρ) ≤ S(ρ'') + S(ρ,
  E₂∘E₁)` (composite eq. (12.144));
* `coherentInfoComp_le_vonNeumannEntropy` — `State.coherentInfoComp_le_vonNeumannEntropy` : `I(ρ,
  E₂∘E₁) ≤ S(ρ)` (composite first-stage data processing bound, from the triangle on `R''Q''`).
* `dilatedJoint` — the un-traced dilation on `(A ⊗ B) ⊗ C` (`State.dilatedChannelOnRight` before its
  final trace);
* `entropyExchangeComp_le_entropyExchange_add_entropyExchange`
* `entropyExchange_le_entropyExchangeComp_add_entropyExchange`
* `entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp`
* `entropyExchange_dilatedChannel_le_vonNeumannEntropy_add_dilatedChannelComp` — the explicit
  second-stage single-operation theorems (operation `E₂` on `ρ' = ρ.dilatedChannel U₁ ω₁`):
  `State.entropyExchange_dilatedChannel_le_vonNeumannEntropy_add_dilatedChannelComp` `S(ρ', E₂) ≤
  S(ρ') + S(ρ'')` and
  `State.vonNeumannEntropy_dilatedChannel_le_dilatedChannelComp_add_entropyExchange` `S(ρ') ≤ S(ρ'')
  + S(ρ', E₂)` (second-stage eq. (12.144)), thin instantiations of the single-operation lemmas.
* `vonNeumannEntropy_dilatedChannel_le_dilatedChannelComp_add_entropyExchange`
* `crossEnvEntropy` — the reference–second-environment entropy `S(R''E₂'')`, defined directly as the
  von Neumann entropy of the `R ⊗ C₂`-marginal of the joint state `τ = σ₁.dilatedJoint U₂ ω₂` (`σ₁ =
  (refPurify ρ).dilatedChannelOnRight U₁ ω₁`), i.e. `τ` with the *middle* system `Q` traced out.
* `crossEnvEntropy_le_vonNeumannEntropy_add_entropyExchange_dilatedChannel`
* `vonNeumannEntropy_le_crossEnvEntropy_add_entropyExchange_dilatedChannel`
* `entropyExchange_dilatedChannel_le_crossEnvEntropy_add_vonNeumannEntropy`
-/

noncomputable section

namespace AxQM

variable {Q C : QSystem}

/-! ### Single-operation inequalities

These hold for any one operation `E` (dilation `(U, ω)`); applied to `(ρ, E₁)` they are the first
stage of the process, applied to `(ρ', E₂)` the second. -/

/-- **Subadditivity bound on the entropy exchange** (Nielsen & Chuang §12.4, a subadditivity
combination for the process of Exercise 12.15). For a state `ρ` on `Q` and an operation `E`
presented by its dilation `(U, ω)`,

`S(ρ, E) ≤ S(ρ) + S(E(ρ))`.
-/
theorem State.entropyExchange_le_vonNeumannEntropy_add_dilatedChannel (ρ : State Q)
    (U : Evolution (Q ⊗ C)) (ω : PureState C) :
    ρ.entropyExchange U ω ≤ ρ.vonNeumannEntropy + (ρ.dilatedChannel U ω).vonNeumannEntropy := sorry

/-- **N&C eq. (12.144): `ΔS + S(ρ, E) ≥ 0`** — the change in the system entropy plus the entropy
exchange is non-negative (an "eminently reasonable statement in accord with the second law of
thermodynamics", N&C p. 568). Stated as

`S(ρ) ≤ S(E(ρ)) + S(ρ, E)`

(with `ΔS = S(E(ρ)) − S(ρ)`).
-/
theorem State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange (ρ : State Q)
    (U : Evolution (Q ⊗ C)) (ω : PureState C) :
    ρ.vonNeumannEntropy ≤ (ρ.dilatedChannel U ω).vonNeumannEntropy + ρ.entropyExchange U ω := sorry

/-! ### Composite process

The two-stage output `ρ'' = (E₂ ∘ E₁)(ρ)` and its entropy exchange `S(ρ, E₂∘E₁)`, with the same
subadditivity/triangle inequalities read off the twice-processed reference–system state `R''Q''`. -/

/-- The **composite output** `ρ'' = (E₂ ∘ E₁)(ρ)` of the two-stage process. -/
def State.dilatedChannelComp (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : State Q :=
  (ρ.dilatedChannel U₁ ω₁).dilatedChannel U₂ ω₂

/-- The **entropy exchange of the two-stage composite operation** `S(ρ, E₂ ∘ E₁) = S(R''Q'')`
(Nielsen & Chuang eq. (12.130), purification form). By the framework's purification definition
it equals the entropy of the composite environment `E₁E₂` after both stages, `S(ρ, E₂ ∘ E₁) =
S(E₁''E₂'')`, and it enters `State.coherentInfoComp` as `I(ρ, E₂∘E₁) = S(ρ'') − S(ρ, E₂∘E₁)`. -/
def State.entropyExchangeComp (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : ℝ :=
  ((ρ.refPurify.toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂).vonNeumannEntropy

/-- **Subadditivity bound on the composite entropy exchange**: for the two-stage process of Exercise
12.15,

`S(ρ, E₂ ∘ E₁) ≤ S(ρ) + S(ρ'')`.
-/
theorem State.entropyExchangeComp_le_vonNeumannEntropy_add_dilatedChannelComp (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ ≤
      ρ.vonNeumannEntropy + (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy := sorry

/-- **Composite form of N&C eq. (12.144)**: for the two-stage process,

`S(ρ) ≤ S(ρ'') + S(ρ, E₂ ∘ E₁)`. -/
theorem State.vonNeumannEntropy_le_dilatedChannelComp_add_entropyExchangeComp (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.vonNeumannEntropy ≤
      (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy + ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ :=
        sorry

/-- **Composite first-stage data-processing bound**: for the two-stage process,

`I(ρ, E₂ ∘ E₁) ≤ S(ρ)`.

It also follows from the merged chain `S(ρ) ≥ I(ρ, E₁) ≥ I(ρ, E₂∘E₁)`; the direct derivation
from the triangle inequality is recorded as one of the Exercise 12.15 combinations.
-/
theorem State.coherentInfoComp_le_vonNeumannEntropy (ρ : State Q) (U₁ : Evolution (Q ⊗ C))
    (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.coherentInfoComp U₁ ω₁ U₂ ω₂ ≤ ρ.vonNeumannEntropy := sorry

/-! ### Two-environment infrastructure: the joint dilation and its environment marginal

The genuinely two-environment combinations of Exercise 12.15 — the ones relating all *three*
entropy exchanges `S(ρ, E₁)`, `S(ρ', E₂)`, `S(ρ, E₂∘E₁)` — cannot be read off a single
reference–system bipartition, because `S(ρ', E₂)` uses a *fresh* purification of the intermediate
state `ρ'`. Following N&C's four-system argument, they live on the state that keeps the **second
environment `C₂`** explicit. We build that state as the **un-traced** dilation `State.dilatedJoint`
(exactly `State.dilatedChannelOnRight` *before* its final partial trace). -/

variable {A B : QSystem}

/-- **The joint state of a channel dilated on the right factor, keeping its environment.** For a
bipartite state `ρ` on `A ⊗ B`, a unitary `U` on `B ⊗ C` and a pure ancilla `ω` on `C`, this is
`(I_A ⊗ U)(ρ ⊗ |ω⟩⟨ω|)(I_A ⊗ U)†` on `(A ⊗ B) ⊗ C` — the state that
`State.dilatedChannelOnRight` traces its environment `C` out of. -/
def State.dilatedJoint (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C)) (ω : PureState C) :
    State ((A ⊗ B) ⊗ C) :=
  (((Evolution.id (S := A)).tmul U).evolve
      (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState))).congr (QSystem.assoc A B C)

/-! ### Entropy-exchange triangle inequalities (all three entropy exchanges) -/

/-- **Subadditivity of the entropy exchange** — the entropy-exchange triangle inequality of
Exercise 12.15: for the two-stage process `ρ → ρ' = E₁(ρ) → ρ'' = (E₂∘E₁)(ρ)`,

`S(ρ, E₂∘E₁) ≤ S(ρ, E₁) + S(ρ', E₂)`.

The joint environment `E₁E₂` is no more disordered than its parts. -/
theorem State.entropyExchangeComp_le_entropyExchange_add_entropyExchange (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ ≤
      ρ.entropyExchange U₁ ω₁ + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := sorry

/-- **Araki–Lieb companion of entropy-exchange subadditivity**: for the two-stage process,

`S(ρ, E₁) ≤ S(ρ, E₂∘E₁) + S(ρ', E₂)`. -/
theorem State.entropyExchange_le_entropyExchangeComp_add_entropyExchange (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.entropyExchange U₁ ω₁ ≤
      ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := sorry

/-- **Second Araki–Lieb companion of entropy-exchange subadditivity**: for the two-stage process,

`S(ρ', E₂) ≤ S(ρ, E₁) + S(ρ, E₂∘E₁)`.

The three companions together are the full triangle
`|S(ρ, E₁) − S(ρ', E₂)| ≤ S(ρ, E₂∘E₁) ≤ S(ρ, E₁) + S(ρ', E₂)` for the entropy exchanges. -/
theorem State.entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ ≤
      ρ.entropyExchange U₁ ω₁ + ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ := sorry

/-! ### Explicit second-stage single-operation inequalities

The single-operation inequalities of §12.4 (this file's
`State.entropyExchange_le_..._dilatedChannel` and
`State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange`) applied to the **second stage**
— operation `E₂` on the intermediate state `ρ' = E₁(ρ) = ρ.dilatedChannel U₁ ω₁` — named for
citation, with the third entropy exchange `S(ρ', E₂)` and the final output
`ρ'' = ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂`. -/

/-- **Second-stage subadditivity bound on the entropy exchange**. -/
theorem State.entropyExchange_dilatedChannel_le_vonNeumannEntropy_add_dilatedChannelComp
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ ≤
      (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy +
        (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy := sorry

/-- **Second-stage form of N&C eq. (12.144)**. -/
theorem State.vonNeumannEntropy_dilatedChannel_le_dilatedChannelComp_add_entropyExchange
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy ≤
      (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy +
        (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := sorry

/-! ### The non-expressible quantity: the prescription for `S(Q''E₁'') = S(R''E₂'')`

Every quantity appearing in the subadditivity/SSA combinations of the two-stage process is a
marginal entropy of the four-system state `R''Q''E₁''E₂''` (pure, since `R` purifies the input and
the environments start pure). All but one reduce to `S(ρ), S(ρ'), S(ρ'')` and the three entropy
exchanges via complementary-marginal purity; the exception is the pair entropy
`S(Q''E₁'') = S(R''E₂'')`. The exercise asks for a prescription to compute it from `ρ` and the
operation elements. We supply it as
`State.crossEnvEntropy`, the von Neumann entropy of the `R ⊗ C₂`-marginal of the joint state
`τ = σ₁.dilatedJoint U₂ ω₂` — `τ` with its middle system `Q` traced out — and record the
inequalities in which it appears. -/

/-- **The reference–second-environment entropy `S(R''E₂'')`** — the prescription (Nielsen & Chuang
Exercise 12.15, escape clause) for the one quantity of the two-stage process `ρ → ρ' = E₁(ρ) →
ρ'' = (E₂∘E₁)(ρ)` that no combination of subadditivity/strong subadditivity expresses in `S(ρ),
S(ρ'), S(ρ'')` and the entropy exchanges `S(ρ, E₁), S(ρ', E₂), S(ρ, E₂∘E₁)`.

In the four-system picture `R''Q''E₁''E₂''` this quantity is `S(R''E₂'')`, equal by global
purity to `S(Q''E₁'')` but not to any of the six standard quantities. It is defined here
directly as the von Neumann entropy of the `R ⊗ C₂`-marginal of the joint dilated state `τ =
σ₁.dilatedJoint U₂ ω₂`, where `σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁` is the
reference–system state after `E₁` and `C₂` is the second environment — i.e. `τ` (on `(R ⊗ Q) ⊗
C₂`) with the *middle* system `Q` traced out. Because `τ` is a fixed function of `ρ` and the
dilations `(U₁, ω₁), (U₂, ω₂)` that present the operations `{Eⱼ}, {Fₖ}`, this is precisely N&C's
requested prescription: a definite real number computed from `ρ` and the operation elements.
-/
def State.crossEnvEntropy (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : ℝ :=
  (State.congr (QSystem.assoc D _ Q)
      (State.congr (QSystem.Iso.comm _ D)
        (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂))).reducedLeft
    |>.vonNeumannEntropy

/-! ### Marginals of the `R ⊗ C₂` block

The `R ⊗ C₂`-block whose entropy is `State.crossEnvEntropy` is
`τ = σ₁.dilatedJoint U₂ ω₂` reshaped so `Q` is the outer factor and traced off
(`σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`). Its two marginals carry the two *expressible*
quantities: the `C₂`-side (`.reducedLeft.reducedLeft`) is `E₂''` with entropy `S(ρ', E₂)`, and the
`R`-side (`.reducedLeft.reducedRight`) is `R''` with entropy `S(ρ)`. -/

/-- **Subadditivity for the escape quantity**: applying subadditivity to the pair `(R'', E₂'')` —
the two-stage analogue of N&C eq. (12.143) — gives

`S(R''E₂'') ≤ S(ρ) + S(ρ', E₂)`.

The two marginals of the `R ⊗ C₂`-block are extracted from the joint state `τ` by the associator
/ commutator reduced-state lemmas.
-/
theorem State.crossEnvEntropy_le_vonNeumannEntropy_add_entropyExchange_dilatedChannel
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.crossEnvEntropy U₁ ω₁ U₂ ω₂ ≤
      ρ.vonNeumannEntropy + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := sorry

/-- **Araki–Lieb lower bound on `S(ρ)` by the escape quantity**: for the two-stage process,

`S(ρ) ≤ S(R''E₂'') + S(ρ', E₂)`. -/
theorem State.vonNeumannEntropy_le_crossEnvEntropy_add_entropyExchange_dilatedChannel
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.vonNeumannEntropy ≤
      ρ.crossEnvEntropy U₁ ω₁ U₂ ω₂ + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := sorry

/-- **Araki–Lieb lower bound on `S(ρ', E₂)` by the escape quantity**: for the two-stage process,

`S(ρ', E₂) ≤ S(R''E₂'') + S(ρ)`.

With its two siblings this is the full triangle `|S(ρ) − S(ρ', E₂)| ≤ S(R''E₂'') ≤ S(ρ) + S(ρ',
E₂)`, the complete family of inequalities relating the escape quantity to the two standard
quantities that flank it.
-/
theorem State.entropyExchange_dilatedChannel_le_crossEnvEntropy_add_vonNeumannEntropy
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ ≤
      ρ.crossEnvEntropy U₁ ω₁ U₂ ω₂ + ρ.vonNeumannEntropy := sorry

end AxQM
