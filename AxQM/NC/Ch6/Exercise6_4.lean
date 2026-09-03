/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GroverSearchMeasurement

/-!
# Nielsen & Chuang, Exercise 6.4 (the quantum search algorithm for multiple solutions)

*(N&C p. 254.)*

Give explicit steps for the quantum search algorithm for multiple solutions (1<M<N/2).

* `grover_multipleSolutions_bornProb_solution_ge_half`
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.4 — the multiple-solution quantum search succeeds with
probability `≥ ½` in `O(√(N/M))` steps.** For an `M`-solution search problem with Grover rotation
angle `θ` given by `sin(θ/2) = √(M/N)` (N&C Eq. 6.10) and `1 ≤ M ≤ N/2` (encoded as `0 < M`,
`2M ≤ N`, and `0 < θ ≤ π/2`), there is a number of Grover iterations `R` such that:

* **success** — measuring the state `Gᴿ|ψ⟩` (the register after `R` Grover iterations, prepared as
  in steps 1–3 of the algorithm) in the computational basis returns a *solution* (the `|β⟩`
  outcome) with Born probability at least one half; and
* **cost** — only `R ≤ (π/4)√(N/M) = O(√(N/M))` iterations, hence oracle calls, are used — the
  quadratic speedup over the `O(N/M)` classical cost. -/
theorem grover_multipleSolutions_bornProb_solution_ge_half
    (N M θ : ℝ) (hM : 0 < M) (hMN : 2 * M ≤ N)
    (hθ0 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    (hsin : Real.sin (θ / 2) = Real.sqrt (M / N)) :
    ∃ R : ℕ, (1 : ℝ) / 2 ≤ groverSolutionMeasurement.bornProb (groverFinalState θ R).toState 1
      ∧ (R : ℝ) ≤ Real.pi / 4 * Real.sqrt (N / M) := sorry

end AxQM
