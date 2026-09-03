/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-!
# Nielsen & Chuang, Theorem 9.7 (Strong concavity of the fidelity)

*(N&C p. 414.)*

Strong concavity of fidelity for state mixtures with probability distributions.

* `sum_sqrt_mul_fidelity_le_fidelity_mix` — `∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ)` for
  probability distributions `p, q` and families of states `ρ, σ`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Strong concavity of the fidelity** (Nielsen & Chuang, Theorem 9.7, `(9.92)`): for probability
distributions `p, q` over a common finite index set and families of states `ρ, σ`,
`∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ)`.
-/
theorem State.sum_sqrt_mul_fidelity_le_fidelity_mix {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) (ρ σ : ι → State S) :
    ∑ i, Real.sqrt (p i * q i) * (ρ i).fidelity (σ i)
      ≤ (State.mix p hp hps ρ).fidelity (State.mix q hq hqs σ) := sorry

end AxQM
