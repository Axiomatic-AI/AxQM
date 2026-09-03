/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Mixture
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Theorem 9.3 (Strong convexity of the trace distance)

*(N&C p. 407.)*

Strong convexity of trace distance for mixtures of states and probability distributions.

* `traceDistance_mix_le` — Theorem 9.3, `(9.46)`: the strong-convexity bound.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Theorem 9.3 (Strong convexity of the trace distance, `(9.46)`).** For
probability distributions `p, q : ι → ℝ` over a finite index set and families of states
`ρ, σ : ι → State S`, the trace distance between the mixtures is bounded by the classical
distance of the weights plus the `p`-average of the componentwise distances:
`D(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ) ≤ D(p, q) + ∑ᵢ pᵢ D(ρᵢ, σᵢ)`. -/
theorem State.traceDistance_mix_le {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (ρ σ : ι → State S) :
    (State.mix p hp hpsum ρ).traceDistance (State.mix q hq hqsum σ)
      ≤ Concrete.classicalTraceDist p q + ∑ i, p i * (ρ i).traceDistance (σ i) := sorry

end AxQM
