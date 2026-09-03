/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SphericalAverage
import AxQM.Concrete.PauliCommutator
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: the dipolar coupling `H^D_{1,2}` and its vanishing spherical average

This file defines the **through-space dipolar coupling Hamiltonian** of two spin-½ nuclei and
states that its spherical average over the internuclear direction vanishes.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker BigOperators

/-- The **isotropic coupling** `σ⃗₁·σ⃗₂ = ∑ₐ σ^a ⊗ σ^a`, the direction-independent term of `H^D`. -/
noncomputable def spinSpinCoupling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ a, pauliSigma a ⊗ₖ pauliSigma a

/-- The **anisotropic coupling** `(σ⃗₁·n̂)(σ⃗₂·n̂) = (n·σ) ⊗ (n·σ)`, the direction-dependent term
of `H^D`. -/
noncomputable def spinDirProduct (n : Fin 3 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliDot n ⊗ₖ pauliDot n

/-- The **dipolar bracket** `σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂)`, the `n̂`-dependent operator inside
`H^D_{1,2}` (Nielsen & Chuang eq. 7.136). -/
noncomputable def dipolarBracket (n : Fin 3 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinSpinCoupling - (3 : ℂ) • spinDirProduct n

/-- The **through-space dipolar coupling Hamiltonian** `H^D_{1,2}(n̂)` of two spin-½ nuclei a
distance `r` apart along `n̂`, with gyromagnetic factors `γ₁, γ₂` and `ℏ` (Nielsen & Chuang
eq. 7.136): `(γ₁ γ₂ ℏ / 4r³) · [σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂)]`. -/
noncomputable def dipolarCoupling (γ₁ γ₂ ℏ r : ℝ) (n : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((γ₁ * γ₂ * ℏ / (4 * r ^ 3) : ℝ) : ℂ) • dipolarBracket n

/-- The **entrywise spherical average** of a matrix-valued function of the unit direction `n̂`. -/
noncomputable def matrixSphericalAverage {m p : Type*}
    (F : (Fin 3 → ℝ) → Matrix m p ℂ) : Matrix m p ℂ :=
  Matrix.of fun i j => sphericalAverage (fun n => F n i j)

/-- **Nielsen & Chuang, Exercise 7.35 (motional narrowing).** The spherical average of the dipolar
coupling Hamiltonian `H^D_{1,2}` over the internuclear direction `n̂` is the **zero** matrix, for
every choice of the physical constants `γ₁, γ₂, ℏ, r`. -/
theorem dipolarCoupling_matrixSphericalAverage (γ₁ γ₂ ℏ r : ℝ) :
    matrixSphericalAverage (dipolarCoupling γ₁ γ₂ ℏ r) = 0 := sorry

end AxQM.Concrete
