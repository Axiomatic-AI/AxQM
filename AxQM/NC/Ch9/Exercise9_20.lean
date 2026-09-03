/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_7

/-!
# Nielsen & Chuang, Exercise 9.20 (Concavity of the fidelity)

*(N&C p. 415.)*

Prove fidelity concave in first entry.

* `fidelity_concaveLeft`
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Concavity of the fidelity in the first entry** (Nielsen & Chuang, Exercise 9.20, `(9.96)`):
for a probability distribution `p` over a finite index set, a family of states `ρ` and a fixed
state `σ`, `∑ᵢ pᵢ F(ρᵢ, σ) ≤ F(∑ᵢ pᵢ ρᵢ, σ)`.

Mixing in the first argument never decreases the fidelity below the `pᵢ`-weighted average of the
componentwise fidelities.
-/
theorem State.fidelity_concaveLeft {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (ρ : ι → State S) (σ : State S) :
    ∑ i, p i * (ρ i).fidelity σ ≤ (State.mix p hp hps ρ).fidelity σ := sorry

end AxQM
