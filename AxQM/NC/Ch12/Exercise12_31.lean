/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Problem12_1
import AxQM.Core.HolevoChi
import AxQM.Basic.API.PureMarginalEntropy

/-!
# Nielsen & Chuang, Exercise 12.31 — `S(ρ)` bounds Eve's mutual information

*(N&C p. 594.)*

Show S(rho) bounds Eve's mutual info by giving Eve full control of channel.

* `eavesdropper_mutualInfo_le_vonNeumannEntropy` — Eve's classical mutual information with the key
  is at most `S(ρ)`.
-/

noncomputable section

namespace AxQM

/-- **N&C Exercise 12.31 — `S(ρ)` bounds Eve's mutual information with the key.**

Assume the worst about the eavesdropper Eve by giving her all control of the channel: the global
state of Alice and Bob's system `AB` and Eve's system `E` is a *pure* state `ψ`, whose left
marginal is Alice and Bob's shared state `ρ = tr_E |ψ⟩⟨ψ|`. Let `{pₖ, σₖ}` be Eve's ensemble of
conditional states associated with the possible key values `k` produced by Alice and Bob's
measurements; by consistency it reconstructs Eve's marginal, `∑ₖ pₖ σₖ = tr_{AB} |ψ⟩⟨ψ|`.

`H(K : Eve) ≤ S(ρ)`.

Holding for every ensemble decomposing `ρ_E` and every measurement, it bounds any strategy Eve
may employ.
-/
theorem PureState.eavesdropper_mutualInfo_le_vonNeumannEntropy
    {AB E : QSystem} (ψ : PureState (AB.compose E))
    {ρ : State AB} (hρ : ψ.toState.reducedLeft = ρ)
    {r : ℕ} [NeZero r] {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (σ : κ → State E) (hσ : State.mix p hp hsum σ = ψ.toState.reducedRight)
    (m : Measurement (Fin r) E) :
    (Real.mutualInfo fun xy => p xy.1 * m.bornProb (σ xy.1) xy.2) ≤ ρ.vonNeumannEntropy := sorry

end AxQM
