/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.MeasurementCoarseGrain
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.Associator
import AxQM.Basic.SystemIso
import AxQM.Basic.Evolution

/-!
# Nielsen & Chuang, Problem 8.2 (Teleportation as a quantum operation)

*(N&C p. 395.)*

Show teleportation via imperfect entanglement induces operation Ê_m reversible by R_m to recover ρ.

* `teleportationJointState`
* `teleportationFineProb`
* `teleportationProb`
* `teleportationProb_sum_eq_one`
* `teleportationProb_nonneg`
* `teleportationFineInducedState`
* `teleportationInducedState`
* `teleportationRecovery`
* `TeleportationRecovers`
* `teleportationInducedState_injective_of_recovers`
-/

noncomputable section

namespace AxQM

universe uD

variable {A B C : QSystem} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- **The regrouped global initial state** of Problem 8.2: the product `ρ ⊗ σ` of the input state
`ρ` of system 1 with the (imperfect) resource state `σ` on systems 2⊗3, transported from the natural
grouping `A ⊗ (B ⊗ C)` to `(A ⊗ B) ⊗ C` via the associator `QSystem.assoc A B C`, so that Alice's
pair (systems 1,2 = `A ⊗ B`) is a single tensor factor available for measurement. -/
def teleportationJointState (ρ : State A) (σ : State (B ⊗ C)) : State ((A ⊗ B) ⊗ C) :=
  State.congr (QSystem.assoc A B C) (ρ ⊗ σ)

/-- **The fine-outcome probability** `p(k)`. The induced (coarse) probability `teleportationProb` is
the fibre-sum of these over `g⁻¹(i)`. -/
def teleportationFineProb (m : Measurement κ (A ⊗ B)) (σ : State (B ⊗ C)) (ρ : State A)
    (k : κ) : ℝ :=
  (m.onLeft C).bornProb (teleportationJointState ρ σ) k

/-- **The induced outcome probability** `p(i) = tr[Êᵢ(ρ)]` (N&C 8.189): the Born probability that
Alice reports classical result `i`, i.e. the Born probability of the *coarse-grained* lifted
measurement `(m.onLeft C).coarseGrain g` on the regrouped joint state. -/
def teleportationProb (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C)) (ρ : State A)
    (i : ι) : ℝ :=
  ((m.onLeft C).coarseGrain g).bornProb (teleportationJointState ρ σ) i

/-- **The induced family `{Êᵢ}` is collectively trace-preserving:** the induced outcome
probabilities sum to one, `Σᵢ tr[Êᵢ(ρ)] = 1`. This is the Born-rule normalisation for the
coarse-grained lifted measurement `(m.onLeft C).coarseGrain g`, and records that Alice's instrument
induces a *complete* family of operations on the input–output pair (system 1 → system 3). -/
theorem teleportationProb_sum_eq_one (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) : ∑ i, teleportationProb m g σ ρ i = 1 := sorry

/-- Each induced outcome probability is non-negative. -/
theorem teleportationProb_nonneg (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) (i : ι) : 0 ≤ teleportationProb m g σ ρ i :=
  ((m.onLeft C).coarseGrain g).bornProb_nonneg (teleportationJointState ρ σ) i

/-- **The fine-outcome induced state** — the single-Kraus building block of `Êᵢ`. For a *possible*
fine outcome `k` (`p(k) ≠ 0`) it is the normalised final state of system 3, the marginal on `C`
(tracing out Alice's `A ⊗ B`) of the post-measurement joint state `(m.onLeft C).postMeasurement …`,
i.e. `(Mₖ ρ Mₖ† / p(k))`'s system-3 marginal. For an *impossible* fine outcome (`p(k) = 0`) it is an
inert placeholder (`σ`'s system-3 marginal): such `k` carries conditional weight `0` in the mixture
`teleportationInducedState` and so never contributes to the induced operation. -/
def teleportationFineInducedState (m : Measurement κ (A ⊗ B)) (σ : State (B ⊗ C)) (ρ : State A)
    (k : κ) : State C := by
  classical
  exact if hk : teleportationFineProb m σ ρ k = 0 then σ.reducedRight
    else ((m.onLeft C).postMeasurement (teleportationJointState ρ σ) k hk).reducedRight

/-- **The induced operation `Êᵢ`, as its normalised output** (N&C Problem 8.2, eq. 8.189): the final
state of system 3 (Bob's) after Alice measures systems 1,2 with her instrument and reports classical
result `i` (`hp : p(i) ≠ 0`), namely `Êᵢ(ρ) / tr[Êᵢ(ρ)]`.

It is the probabilistic **mixture**, over the fibre `g⁻¹(i)`, of the fine induced states
`teleportationFineInducedState` weighted by the conditional probabilities `p(k) / p(i)` — precisely
the normalised fibre-sum `(Σ_{k : g k = i} p(k)·(system-3 marginal of MₖρMₖ†/p(k))) / p(i)`, the
state Bob holds and to which N&C's recovery `Rᵢ` is applied in (8.189). The map
`ρ ↦ teleportationInducedState m g σ ρ i hp` is the induced operation `Êᵢ` relating the initial
state of system 1 to the final state of system 3. -/
def teleportationInducedState (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) (i : ι) (hp : teleportationProb m g σ ρ i ≠ 0) : State C :=
  State.mix
    (fun k => if g k = i then teleportationFineProb m σ ρ k / teleportationProb m g σ ρ i else 0)
    (fun k => by
      change 0 ≤ if g k = i then teleportationFineProb m σ ρ k / teleportationProb m g σ ρ i else 0
      split_ifs with hk
      · exact div_nonneg ((m.onLeft C).bornProb_nonneg _ k) (teleportationProb_nonneg m g σ ρ i)
      · exact le_refl 0)
    (by
      have h := (m.onLeft C).coarseGrain_bornProb g (teleportationJointState ρ σ) i
      simp only [teleportationProb, teleportationFineProb]
      rw [← Finset.sum_filter, ← Finset.sum_div, ← h]
      exact div_self hp)
    (fun k => teleportationFineInducedState m σ ρ k)

/-- **Bob's recovery operation `Rᵢ`, applied to a state of system 3** (N&C Problem 8.2, eq. 8.189).
A general trace-preserving quantum operation on Bob's system 3 (`C`) is realised in the
API in the **environment/Stinespring form** (the shape N&C use for quantum operations, eq. 8.6).
The resulting state of system 3 is
relabelled to system 1 (`A`) through the physical identification `e : A ≃ₛ C` of the two
single-qubit systems, so that it can be compared with the input `ρ : State A`. Every
trace-preserving quantum operation arises this way, so quantifying over `(D, ω, U)` is exactly
quantifying over N&C's trace-preserving quantum operation `Rᵢ`. The output is a genuine `State`
(trace one), so `Rᵢ` is trace-preserving by construction. -/
def teleportationRecovery (e : A ≃ₛ C) {D : QSystem.{uD}} (ω : State D) (U : Evolution (C ⊗ D))
    (τ : State C) : State A :=
  ((U.evolve (τ ⊗ ω)).reducedLeft).congr e.symm

/-- **The reversibility criterion for Alice's outcome `i`** — Nielsen & Chuang, Problem 8.2, eq.
(8.189). The recovery is chosen once for the outcome (existentially quantified *outside* the `∀
ρ`), reflecting that Bob applies it knowing only the classical result `i`, never Alice's unknown
`ρ`. -/
def TeleportationRecovers (e : A ≃ₛ C) (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (i : ι) : Prop :=
  ∃ (D : QSystem.{uD}) (ω : State D) (U : Evolution (C ⊗ D)),
    ∀ (ρ : State A) (hp : teleportationProb m g σ ρ i ≠ 0),
      teleportationRecovery e ω U (teleportationInducedState m g σ ρ i hp) = ρ

/-- **Teleportation success forces the induced operation to be injective on inputs** (N&C Problem
8.2). If Bob can reverse `Êᵢ` for outcome `i` (`TeleportationRecovers`), then distinct inputs
`ρ` produce distinct normalised final states of system 3. This is the precise sense in which
*teleportation is accomplished* — Bob's final state determines Alice's original `ρ` uniquely, so
no information about `ρ` is lost in transit. -/
theorem teleportationInducedState_injective_of_recovers (e : A ≃ₛ C) (m : Measurement κ (A ⊗ B))
    (g : κ → ι) (σ : State (B ⊗ C)) (i : ι) (h : TeleportationRecovers e m g σ i) {ρ₁ ρ₂ : State A}
    (hp₁ : teleportationProb m g σ ρ₁ i ≠ 0) (hp₂ : teleportationProb m g σ ρ₂ i ≠ 0)
    (hτ : teleportationInducedState m g σ ρ₁ i hp₁ = teleportationInducedState m g σ ρ₂ i hp₂) :
    ρ₁ = ρ₂ := sorry

end AxQM
