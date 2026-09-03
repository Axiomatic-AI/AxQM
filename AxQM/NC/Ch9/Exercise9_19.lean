/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_7

/-!
# Nielsen & Chuang, Exercise 9.19 (Joint concavity of the fidelity)

*(N&C p. 415.)*

Prove fidelity jointly concave.

* `sum_mul_fidelity_le_fidelity_mix` — `∑ᵢ pᵢ F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ)` for a probability
  distribution `p` and families of states `ρ, σ`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Joint concavity of the fidelity** (Nielsen & Chuang, Exercise 9.19, `(9.95)`): for a
probability distribution `p` over a finite index set and families of states `ρ, σ`, `∑ᵢ pᵢ F(ρᵢ,
σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ)`.

Mixing both arguments with the *same* distribution `p` never decreases the fidelity below the
`pᵢ`-weighted average of the componentwise fidelities.
-/
theorem State.sum_mul_fidelity_le_fidelity_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1) (ρ σ : ι → State S) :
    ∑ i, p i * (ρ i).fidelity (σ i)
      ≤ (State.mix p hp hps ρ).fidelity (State.mix p hp hps σ) := sorry

end AxQM
