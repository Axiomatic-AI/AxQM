/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationComposition

/-!
# Concrete: the search-simulation step `U(Δt)` in Bloch/Pauli form (Nielsen & Chuang, Eq. 6.25)

Nielsen & Chuang, §6.2, study quantum search as the simulation of the Hamiltonian
`H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18). The lowest-order simulation step is the product of the two
projector-Hamiltonian propagators, whose reduced form is eq. 6.25.

## Contents

* `searchStepAxis` — the axis vector `c (a+b)/2 + s (a×b)/2` of eq. 6.25.
* `searchStepReduced` — the right-hand side of eq. 6.25 as an explicit matrix (the scalar
  `c² − s² a·b` times `I`, minus `2is` times `searchStepAxis · σ`).
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **axis vector of eq. 6.25**. -/
noncomputable def searchStepAxis (Δt : ℝ) (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Real.cos (Δt / 2) • ((2⁻¹ : ℝ) • (a + b))
    + Real.sin (Δt / 2) • ((2⁻¹ : ℝ) • crossProduct a b)

/-- **The right-hand side of Nielsen & Chuang, Eq. 6.25**, as an explicit `2 × 2` complex matrix. -/
noncomputable def searchStepReduced (Δt : ℝ) (a b : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (↑(Real.cos (Δt / 2) ^ 2 - Real.sin (Δt / 2) ^ 2 * (a ⬝ᵥ b)) : ℂ)
      • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    - (2 * (Real.sin (Δt / 2) : ℂ) * Complex.I) • pauliDot (searchStepAxis Δt a b)

end AxQM.Concrete
