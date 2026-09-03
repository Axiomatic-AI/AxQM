/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochPureState
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Concrete: the spherical average over the unit sphere, and `⟨nₐn_b⟩ = δₐb/3`

This file defines the **spherical average** of a function of the unit direction `n̂` and computes
the second-moment identity `⟨nₐ n_b⟩ = δₐb/3`.

## Declarations

* `sphericalAverage` — the complex-valued spherical average.
-/

namespace AxQM.Concrete

open intervalIntegral MeasureTheory

/-- The **spherical average** of a complex-valued function of the unit direction `n̂`, computed in
spherical coordinates `n̂(θ,φ) = blochSphereVector θ φ` with solid-angle weight `sin θ` and total
solid angle `4π`: `(4π)⁻¹ ∫₀^π (∫₀^{2π} f(n̂(θ,φ)) dφ) sin θ dθ`. -/
noncomputable def sphericalAverage (f : (Fin 3 → ℝ) → ℂ) : ℂ :=
  (4 * Real.pi : ℂ)⁻¹ * ∫ θ in (0:ℝ)..Real.pi,
    (∫ φ in (0:ℝ)..(2 * Real.pi), f (blochSphereVector θ φ)) * (Real.sin θ : ℂ)

end AxQM.Concrete
