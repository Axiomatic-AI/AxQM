/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.PauliEigenvectors
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the §1.2 single-qubit pure state and its Bloch vector (N&C, Exercise 2.72(4))

This file records, at the matrix level, the
**§1.2 Bloch-sphere parametrization of a single-qubit pure state**.

## Contents

* `blochKet θ φ` — the column vector `cos(θ/2) |0⟩ + e^{iφ} sin(θ/2) |1⟩` of `ℂ²` (§1.2 eq. 1.4).
* `blochSphereVector θ φ` — the §1.2 Cartesian Bloch vector `(sin θ cos φ, sin θ sin φ, cos θ)`.
* `blochSphereVector_normSq` — it is a **unit vector**, `r₀² + r₁² + r₂² = 1`, so a pure state lies
  on the *surface* of the Bloch ball.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **§1.2 single-qubit pure-state vector** `|ψ(θ,φ)⟩ = cos(θ/2) |0⟩ + e^{iφ} sin(θ/2) |1⟩`
(Nielsen & Chuang eq. 1.4), as a column vector `Fin 2 → ℂ`. Its polar angle `θ` and azimuth `φ`
locate the state on the Bloch sphere. -/
noncomputable def blochKet (θ φ : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos (θ / 2) : ℂ), Complex.exp ((φ : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ)]

/-- The **§1.2 Cartesian Bloch vector** `r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)` of the pure state
`blochKet θ φ`: the spherical-to-Cartesian coordinates of the point `(θ, φ)` on the Bloch sphere
(Nielsen & Chuang §1.2, Figure 1.3), with the `z`-axis along `|0⟩`. -/
noncomputable def blochSphereVector (θ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- **The §1.2 Bloch vector is a unit vector:** `r₀² + r₁² + r₂² = 1` for `r⃗ = blochSphereVector θ
φ`, so a pure state lies on the *surface* `‖r⃗‖ = 1` of the Bloch ball. -/
theorem blochSphereVector_normSq (θ φ : ℝ) :
    blochSphereVector θ φ 0 ^ 2 + blochSphereVector θ φ 1 ^ 2
      + blochSphereVector θ φ 2 ^ 2 = 1 := by
  simp only [blochSphereVector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

end AxQM.Concrete
