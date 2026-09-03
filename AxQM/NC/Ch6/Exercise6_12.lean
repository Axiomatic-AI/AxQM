/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CouplingHamiltonian
import AxQM.Basic.API.SubsetUniformSuperposition

/-!
# Nielsen & Chuang, Exercise 6.12 (alternative Hamiltonian for quantum search)

*(N&C p. 261.)*

For H=|x><psi|+|psi><x|: (1) show O(1) time to rotate |psi> to |x>; (2) simulate H and count oracle
calls.

* `alternativeSearchHamiltonian`
* `alternativeSearchHamiltonian_rotates_uniform_to_solution` — evolving `|ψ⟩` under `H` for the
  constant time `t = π/2` produces the solution state `|x⟩` (up to a global phase): the state
  coincides with `|x⟩`.
* `alternativeSearchHamiltonianSimulation`
* `alternativeSearchHamiltonian_simulation_gateError_pow_le` — its accuracy, eq. 4.107 in Box 4.1's
  error notation: `E(U_Δtᵐ, exp(−2imH·Δt)) ≤ m·α·Δt³` for some `α ≥ 0` and every `Δt ∈ [0, 1]`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- **The alternative search Hamiltonian** `H = |x⟩⟨ψ| + |ψ⟩⟨x|` (Nielsen & Chuang, Exercise 6.12,
eq. 6.29), for a search space `qudit d` (`N = d` items) with the (unique) solution `x`: `|x⟩ =
quditBasis x` is the solution computational-basis state and `|ψ⟩ = uniformSuperposition d` the
uniform superposition. -/
def alternativeSearchHamiltonian [NeZero d] (x : Fin d) : Observable (qudit d) :=
  (quditBasis x).couplingHamiltonian (uniformSuperposition d)

/-- **Part (1): the alternative search Hamiltonian rotates `|ψ⟩` onto the solution in `O(1)` time.**
Evolving the uniform superposition `|ψ⟩` under `H = |x⟩⟨ψ| + |ψ⟩⟨x|` for the **constant** time
`t = π/2` produces the solution state `|x⟩` (up to a global phase): the density operators
coincide, `(exp(−iH(π/2))|ψ⟩ as a state) = |x⟩`. The observation time `π/2` is *independent of
the register size `N = d`* — this is the `O(1)`-time rotation of Nielsen & Chuang, Exercise
6.12(1). -/
theorem alternativeSearchHamiltonian_rotates_uniform_to_solution [NeZero d] (x : Fin d) :
    (((alternativeSearchHamiltonian x).propagator 1 0 (Real.pi / 2)).evolvePure
        (uniformSuperposition d)).toState
      = (quditBasis x).toState := sorry

/-- **Part (2): the alternative search Hamiltonian is simulated by a symmetric Trotter product**
(Nielsen & Chuang, Exercise 6.12(2), which asks for a quantum simulation of `H`).
The concrete quantum simulation of `H = |x⟩⟨ψ| + |ψ⟩⟨x|`: the symmetric (Strang) Trotter step `U_Δt`
(N&C eq. 4.106) of the propagators of the three projector Hamiltonians of the decomposition
`H = |x+ψ⟩⟨x+ψ| − |x⟩⟨x| − |ψ⟩⟨ψ|`. -/
def alternativeSearchHamiltonianSimulation [NeZero d] (x : Fin d) (Δt : ℝ) : Evolution (qudit d) :=
  (quditBasis x).couplingSymmTrotterStep (uniformSuperposition d) Δt

/-- **Part (2): accuracy of the alternative-Hamiltonian simulation** (Nielsen & Chuang, Exercise
6.12(2), eq. 4.107). Running the symmetric-Trotter simulation
`alternativeSearchHamiltonianSimulation x` for `m` steps approximates the exact evolution
`exp(−2imH·Δt)` under the alternative search Hamiltonian with an error growing at most linearly
in the step count: `E(U_Δtᵐ, exp(−2imH·Δt)) ≤ m·α·Δt³` for some `α ≥ 0` and every `Δt ∈ [0, 1]`,
in Box 4.1's gate-error notation `E(U,V) = ‖U − V‖`. This is the *accuracy* half of the exercise,
whose other half counts the oracle calls. -/
theorem alternativeSearchHamiltonian_simulation_gateError_pow_le [NeZero d] (x : Fin d) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (m : ℕ) (Δt : ℝ), 0 ≤ Δt → Δt ≤ 1 →
      (alternativeSearchHamiltonianSimulation x Δt ^ m).gateError
          ((alternativeSearchHamiltonian x).propagator 1 0 (2 * (m : ℝ) * Δt))
        ≤ (m : ℝ) * α * Δt ^ 3 := sorry

end AxQM
