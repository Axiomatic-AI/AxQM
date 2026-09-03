/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.CascadedMeasurement
import AxQM.Basic.API.CompositeMeasurement

/-!
# AxQM — phase estimation on a superposition input (N&C Exercise 5.8)

Nielsen & Chuang, §5.2.1, Exercise 5.8. The phase estimation algorithm run on a *single* eigenstate
`|u⟩` of `U` (eigenvalue `e^{2πiϕ_u}`) takes `|0⟩|u⟩` to `|φ̃_u⟩|u⟩`, and — for `t` control qubits
chosen per (5.35) — measuring the control register produces an estimate `φ̃_u` accurate to `n` bits
with probability `≥ 1 - ε`. By linearity, on the superposition input `|0⟩ ∑ᵤ c_u |u⟩` the algorithm
outputs the entangled state `∑ᵤ c_u |φ̃_u⟩|u⟩`. Exercise 5.8 asks to show that the probability of
measuring `φ̃_u` accurate to `n` bits is then at least `‖c_u‖² (1 - ε)`.

## Main declarations
* `Measurement.leftAndBasisRight m vb` — the **joint readout** of `C ⊗ S`: measure the control
  register with an arbitrary measurement `m` (in phase estimation, the computational-basis readout
  after the inverse QFT) and the target register in the orthonormal basis `vb`, recording the pair
  of outcomes.
* `phaseEstimationSuperposition_accuracy_ge` — **Exercise 5.8:** summing over a success set `G` of
  control outcomes for eigenstate `k`, the joint probability of measuring `φ̃ₖ` accurately is
  at least `‖cₖ‖² (1 - ε)`, given the single-eigenstate accuracy `1 - ε ≤ ∑_{i ∈ G} p_m(i | φₖ)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {C S : QSystem} {μ ι : Type*} [Fintype μ] [Fintype ι]

/-- **Joint readout of a bipartite register.** Measure the left factor `C` with an arbitrary
measurement `m` and the right factor `S` in the orthonormal basis `vb`, recording the pair of
outcomes `(i, k) ∈ μ × ι`. Realised as the cascade of `m.onLeft S` (measure the control register)
and `(Measurement.ofOrthonormalBasis vb).onRight C` (measure the target in `vb`); the two operators
act on disjoint factors, so their order is immaterial. In phase estimation `C` is the `t`-qubit
control register read out after the inverse QFT, and `vb` is the eigenbasis of `U` on the target. -/
def Measurement.leftAndBasisRight (m : Measurement μ C) (vb : OrthonormalBasis ι ℂ S.space) :
    Measurement (μ × ι) (C ⊗ S) :=
  (m.onLeft S).cascade ((Measurement.ofOrthonormalBasis vb).onRight C)

/-- **Nielsen & Chuang, Exercise 5.8.** Phase estimation on a superposition input. Given the
entangled output `Ψ = ∑ᵤ cᵤ (φ̃ᵤ ⊗ uᵤ)` of phase estimation over the orthonormal eigenbasis `vb`
of `U` (`uᵤ = vb u` the `u`-th eigenstate, `φ̃ᵤ = φ u` its first-register estimate state), a
control- register readout `m`, a chosen eigenstate `k`, and a success set `G` of control
outcomes counting as "accurate to `n` bits" for eigenstate `k` whose single-eigenstate
probability satisfies `1 - ε ≤ ∑_{i ∈ G} p_m(i | φ̃ₖ)` (guaranteed by choosing `t` per (5.35)),
the joint probability of measuring `φ̃ₖ` accurately — control outcome in `G` **and** the target
register collapsing to the `k`-th eigenstate — is at least `‖cₖ‖² (1 - ε)`.

This is the exercise's conclusion: the single-eigenstate guarantee propagates to the
superposition input weighted by `‖cₖ‖²`, the probability that the target register is found in
the eigenstate `k`.
-/
theorem phaseEstimationSuperposition_accuracy_ge (m : Measurement μ C)
    (vb : OrthonormalBasis ι ℂ S.space) (c : ι → ℂ) (φ : ι → PureState C)
    (Ψ : PureState (C ⊗ S)) (hΨ : Ψ.vec = ∑ j, c j • ((φ j).vec ⊗ₜ[ℂ] vb j))
    (k : ι) (G : Finset μ) (ε : ℝ) (hacc : 1 - ε ≤ ∑ i ∈ G, m.bornProb (φ k).toState i) :
    ‖c k‖ ^ 2 * (1 - ε) ≤ ∑ i ∈ G, (m.leftAndBasisRight vb).bornProb Ψ.toState (i, k) := sorry

end AxQM
