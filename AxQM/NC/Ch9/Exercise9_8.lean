/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_3

/-!
# Nielsen & Chuang, Exercise 9.8 (Convexity of the trace distance)

*(N&C p. 408.)*

Show trace distance convex in first input over state mixtures.

* `traceDistance_mix_left_convex` — Exercise 9.8, `(9.51)`: convexity in the first input, `D(∑ᵢ pᵢ
  ρᵢ, σ) ≤ ∑ᵢ pᵢ D(ρᵢ, σ)`.
* `traceDistance_mix_right_convex` — convexity in the second input,
  `D(ρ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρ, σᵢ)`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.8 (Convexity of the trace distance, `(9.51)`).** The trace
distance is convex in its first input: for a probability distribution `p : ι → ℝ` over a finite
index set, a family of states `ρ : ι → State S`, and a fixed state `σ`, `D(∑ᵢ pᵢ ρᵢ, σ) ≤ ∑ᵢ pᵢ
D(ρᵢ, σ)`, i.e. `(State.mix p hp hpsum ρ).traceDistance σ ≤ ∑ᵢ pᵢ (ρᵢ).traceDistance σ`.
-/
theorem State.traceDistance_mix_left_convex {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (ρ : ι → State S) (σ : State S) :
    (State.mix p hp hpsum ρ).traceDistance σ ≤ ∑ i, p i * (ρ i).traceDistance σ := sorry

/-- Convexity of the trace distance in its **second input** (Nielsen & Chuang, Exercise 9.8):
`D(ρ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρ, σᵢ)`.
-/
theorem State.traceDistance_mix_right_convex {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (ρ : State S) (σ : ι → State S) :
    ρ.traceDistance (State.mix p hp hpsum σ) ≤ ∑ i, p i * ρ.traceDistance (σ i) := sorry

end AxQM
