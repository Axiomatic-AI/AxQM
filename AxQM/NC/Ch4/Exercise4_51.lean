/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliStringSimulation

/-!
# Nielsen & Chuang, Exercise 4.51 — simulating `H = X₁ ⊗ Y₂ ⊗ Z₃`

*(N&C p. 210.)*

Construct a circuit to simulate H=X1 (x) Y2 (x) Z3, giving e^{-i dt H}.

* `pauliStringHamiltonian_xyz_propagator_eq_conj` — the propagator `e^{-iΔt H}` of
  `H = X₁ ⊗ Y₂ ⊗ Z₃` equals the basis-change gate `B` composed with the all-`Z` propagator and
  then `B†`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.51.** The propagator `e^{-iΔt H}` of `H = X₁ ⊗ Y₂ ⊗ Z₃` is
implemented by the single-qubit basis-change gate `B = H ⊗ (SH) ⊗ I`, the all-`Z` propagator
`e^{-iΔt (Z⊗Z⊗Z)}` (the Figure 4.19 parity circuit), and the inverse gate `B†`, for arbitrary
`ℏ, t₁, t₂` (the exercise is `ℏ = 1`, `Δt = t₂ - t₁`). Here `pauliStringHamiltonian ![1,2,3] 1` is
the Hamiltonian `X⊗Y⊗Z` and `pauliStringHamiltonian ![3,3,3] 1` is `Z⊗Z⊗Z`. This is an *exact*
equality of gates (not merely up to a global phase).
-/
theorem pauliStringHamiltonian_xyz_propagator_eq_conj (ℏ t₁ t₂ : ℝ) :
    (pauliStringHamiltonian ![1, 2, 3] 1).propagator ℏ t₁ t₂
      = xyzBasisChangeGate.comp
          (((pauliStringHamiltonian ![3, 3, 3] 1).propagator ℏ t₁ t₂).comp
            xyzBasisChangeGate.adjoint) := sorry

end AxQM
