/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SearchSimulationLanding
import AxQM.Concrete.SearchSimulationStep
import AxQM.Concrete.BlochPureState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nielsen & Chuang, Exercise 6.10 (probability-one search by a tuned simulation step)

*(N&C p. 260.)*

Show a suitable dt gives O(sqrt N) query search with final state exactly |x> (prob 1).

* `searchStepEvolution_exactSearch`
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.10 — a tuned `O(√N)`-query search that lands on `|x⟩` exactly
(probability `1`).** For a search space of size `N ≥ 2`, with effective search qubit
`|ψ⟩ = blochPureState θ 0` whose polar angle satisfies `cos θ = 2/N − 1` (the uniform search state
`α|x⟩ + β|y⟩`, `α² = 1/N`, `cos θ = α² − β²`) and target `|x⟩ = blochPureState 0 0 = |0⟩`, there are
a step count `j` and a simulation time-step `Δt ∈ (0, π]` with:

* `1 ≤ j ≤ (π/4 + 1)·√N` — `O(√N)` applications of the search step
  `U(Δt) = searchStepEvolution θ Δt` (hence `O(√N)` oracle calls, each step being `O(1)` calls,
  Figures 6.4/6.5); and the evolved state `U(Δt)^j |ψ⟩` equals the target `|x⟩` exactly.
-/
theorem searchStepEvolution_exactSearch (N : ℕ) (hN : 2 ≤ N) (θ : ℝ)
    (hθcos : Real.cos θ = 2 / (N : ℝ) - 1) :
    ∃ (j : ℕ) (Δt : ℝ), 0 < Δt ∧ Δt ≤ Real.pi ∧ 1 ≤ j ∧
      (j : ℝ) ≤ (Real.pi / 4 + 1) * Real.sqrt N ∧
      ((searchStepEvolution θ Δt ^ j).evolvePure (blochPureState θ 0)).toState
        = (blochPureState 0 0).toState := sorry

end AxQM
