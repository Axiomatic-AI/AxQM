/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SubsetUniformSuperposition
import AxQM.Basic.API.ContinuousSearchHamiltonian

/-!
# Nielsen & Chuang, Exercise 6.11 (multiple-solution continuous quantum search)

*(N&C p. 261.)*

Guess a Hamiltonian solving the continuous-time search problem for M solutions.

* `searchHamiltonianMSolution` — the guessed Hamiltonian `H = |β⟩⟨β| + |ψ⟩⟨ψ|`, with `|β⟩` the
  uniform superposition over the `M` solutions and `|ψ⟩` that over all `N` items.
* `searchHamiltonianMSolution_measure_yields_solution` — measuring the rotated state in the
  computational basis returns a solution (an index in `T`) with total probability `1`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- **The guessed multiple-solution search Hamiltonian** `H = |β⟩⟨β| + |ψ⟩⟨ψ|` (Nielsen & Chuang,
Exercise 6.11), for a search space `qudit d` (`N = d` items) with solution set `T` (`M = |T|`
solutions): `|β⟩ = subsetUniformSuperposition T hT` is the uniform superposition over the solutions
and `|ψ⟩ = uniformSuperposition d` the uniform superposition over all `N` items. It is the two-state
continuous-search Hamiltonian of §6.2 (eq. 6.18) with the single target `|x⟩` replaced by `|β⟩`. -/
def searchHamiltonianMSolution [NeZero d] (T : Finset (Fin d)) (hT : T.Nonempty) :
    Observable (qudit d) :=
  (subsetUniformSuperposition T hT).searchHamiltonian (uniformSuperposition d)

/-- **Measuring the rotated state returns a solution with probability one.** After evolving `|ψ⟩`
under `H = |β⟩⟨β| + |ψ⟩⟨ψ|` for `t = (π/2)√(N/M)`, a computational-basis measurement returns one
of the `M` solutions (an index in `T`) with total probability `1`: the multiple-solution
continuous search *solves* the search problem. -/
theorem searchHamiltonianMSolution_measure_yields_solution [NeZero d]
    (T : Finset (Fin d)) (hT : T.Nonempty) :
    ∑ x ∈ T, (quditMeasurement d).bornProb
        ((((searchHamiltonianMSolution T hT).propagator 1 0
            (Real.pi / 2 * Real.sqrt ((d : ℝ) / T.card))).evolvePure
          (uniformSuperposition d)).toState) x = 1 := sorry

end AxQM
