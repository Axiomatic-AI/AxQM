/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_17

/-!
# Nielsen & Chuang, Exercise 9.23 (Ensemble average fidelity equal to one)

*(N&C p. 419.)*

Show ensemble average fidelity Fbar=1 iff E(rho_j)=rho_j for all j with p_j>0.

* `ensembleAvgFidelity` — the quantity `F̄` of `(9.127)`;
* `ensembleAvgFidelity_eq_one_iff` — `F̄ = 1 ↔ ∀ j, pⱼ > 0 → E(ρⱼ) = ρⱼ`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **ensemble average fidelity** of a channel `E` with respect to a quantum source — a finite
ensemble of density operators `ρ j` prepared with probabilities `p j` (Nielsen & Chuang `(9.127)`):
`F̄ = ∑ⱼ pⱼ F(ρⱼ, E(ρⱼ))²`, the probability-weighted mean of the squared fidelities between each
emitted state and its image under `E`. The squaring of the fidelity is N&C's convention (it makes
`F̄` relate naturally to the entanglement fidelity). Physically `E` is a trace-preserving quantum
operation, but the definition and its properties make sense for any state map `E`. -/
def ensembleAvgFidelity {ι : Type*} [Fintype ι] (p : ι → ℝ) (ρ : ι → State S)
    (E : State S → State S) : ℝ :=
  ∑ j, p j * (ρ j).fidelity (E (ρ j)) ^ 2

/-- **Exercise 9.23.** The ensemble average fidelity of a channel `E` over a source `{(pⱼ, ρⱼ)}`
(probabilities `pⱼ ≥ 0`, `∑ⱼ pⱼ = 1`) satisfies `F̄ = 1` if and only if `E` fixes every emitted
state carried with positive probability, `E(ρⱼ) = ρⱼ` for all `j` with `pⱼ > 0`.
-/
theorem ensembleAvgFidelity_eq_one_iff {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hps : ∑ j, p j = 1) (ρ : ι → State S) (E : State S → State S) :
    ensembleAvgFidelity p ρ E = 1 ↔ ∀ j, 0 < p j → E (ρ j) = ρ j := sorry

end AxQM
