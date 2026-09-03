/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.Core.MeasurementChannel
import AxQM.NC.Ch11.Theorem11_15
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.PartialTrace
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.HolevoMeasurementChannel
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.MeasurementModel
import AxQM.Basic.API.QuditMeasurement
import AxQM.ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Problem 12.1 — an alternate proof of the Holevo bound

*(N&C p. 602.)*

Alternate proof of Holevo bound via chi monotonicity and apparatus operation.

* `holevoChi_reducedLeft_le` — discard the environment `C`: `χ(E∘ρ) = χ_S ≤ χ_{S,C} = χ(U(ρ ⊗ ω)U†)`
  is Part (1) `State.holevoChi_reducedLeft_le` (`E(ρᵢ)` is the `S`-marginal `Tr_C` of `U(ρᵢ ⊗
  ω)U†`);
* `dilatedChannel`
* `holevoChi_dilatedChannel_le`
* `holevoChi_measState_eq_mutualInfo`
* `holevoBound_of_chi_monotone`
-/

noncomputable section

namespace AxQM

variable {A B : QSystem} {ι : Type*} [Fintype ι]
  (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State (A ⊗ B))

/-- **N&C Problem 12.1(1): the Holevo χ quantity decreases under tracing out a subsystem** (eq.
(12.209)). For an ensemble `{pᵢ, ρᵢ}` of states on a bipartite system `A ⊗ B`,

`χ_A ≤ χ_AB`,

where `χ_A` is the Holevo χ of the `A`-marginal ensemble `{pᵢ, (ρᵢ)_A}` and `χ_AB` is the Holevo
χ of the joint ensemble `{pᵢ, ρᵢ}`.
-/
theorem State.holevoChi_reducedLeft_le :
    State.holevoChi p hp hsum (fun i => (ρ i).reducedLeft) ≤ State.holevoChi p hp hsum ρ := sorry

/-- **The output of a dilated quantum operation on a single system.** For a state `ρ` on `S`, a
unitary `U` on `S ⊗ C`, and an environment `C` prepared in the pure state `ω`, this is Nielsen &
Chuang's Chapter-8 dilation `E(ρ) = Tr_C (U (ρ ⊗ |ω⟩⟨ω|) U†)` of a trace-preserving quantum
operation `E` on `S`. Every trace-preserving quantum operation on `S` arises this way (the
environment/Stinespring representation, N&C §8.2.3). -/
noncomputable def State.dilatedChannel {S C : QSystem} (ρ : State S) (U : Evolution (S ⊗ C))
    (ω : PureState C) : State S :=
  (U.evolve (ρ.tmul ω.toState)).reducedLeft

/-- **N&C Problem 12.1(2): the Holevo χ quantity decreases under a quantum operation** (eq.
(12.210)).

`χ′ = χ(E∘ρ) ≤ χ = χ(ρ)`,

where `χ(E∘ρ)` is the Holevo χ of the image ensemble `{pᵢ, E(ρᵢ)}`.
-/
theorem State.holevoChi_dilatedChannel_le {S C : QSystem} {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (U : Evolution (S ⊗ C)) (ω : PureState C) :
    State.holevoChi p hp hsum (fun i => (ρ i).dilatedChannel U ω)
      ≤ State.holevoChi p hp hsum ρ := sorry

/-- **N&C Problem 12.1(3): the Holevo χ quantity of the measurement apparatus equals the classical
mutual information** `H(X : Y)` (which N&C states with no equation number). Alice prepares the state
`ρₓ` with probability `pₓ` (`{pₓ, ρₓ}`, random variable `X`); Bob performs a POVM measurement `m`
with outcome `Y`. Under N&C's apparatus operation `E(ρ ⊗ |0⟩⟨0|) = ∑ᵧ √Eᵧ ρ √Eᵧ ⊗ |y⟩⟨y|`
(eq. (12.211)) the apparatus register `M`
ends in the marginal `Tr_S E(ρₓ ⊗ |0⟩⟨0|) = ∑ᵧ Tr(Eᵧ ρₓ) |y⟩⟨y|`, which is exactly the
measure-and-record outcome channel `m.measState ρₓ`. This theorem states that the Holevo χ of the
apparatus ensemble `{pₓ, m.measState ρₓ}` equals the classical mutual information of the joint
distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ) = pₓ · m.bornProb ρₓ y` of `X` and `Y`:

`χ_M = H(X : Y)`.
-/
theorem State.holevoChi_measState_eq_mutualInfo {S : QSystem} {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : κ → State S)
    (m : Measurement ι S) :
    State.holevoChi p hp hsum (fun x => m.measState (ρ x))
      = Real.mutualInfo (fun xy : κ × ι => p xy.1 * m.bornProb (ρ xy.1) xy.2) := sorry

section HolevoBound

variable {Q : QSystem} {r : ℕ} [NeZero r] {κ : Type*} [Fintype κ]
  (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : κ → State Q)
  (m : Measurement (Fin r) Q)

/-- **N&C Problem 12.1: the Holevo bound** (eq. (12.212)), assembled from Parts (1)–(3) via the
monotonicity of the Holevo χ quantity — the alternate proof developed in this problem. Then the
classical mutual information of the joint distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ)` obeys

`H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`,

This is N&C's alternate route to the Holevo bound, replacing the direct relative-entropy /
data-processing argument by χ monotonicity throughout.
-/
theorem holevoBound_of_chi_monotone :
    Real.mutualInfo (fun xy : κ × Fin r => p xy.1 * m.bornProb (ρ xy.1) xy.2)
      ≤ State.holevoChi p hp hsum ρ := sorry

end HolevoBound

end AxQM
