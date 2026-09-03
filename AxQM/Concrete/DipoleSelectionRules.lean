/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Electric-dipole selection rules — spherical harmonics and the overlap integral (N&C 7.60)

This file develops the concrete special-function mathematics behind **Nielsen & Chuang,
Exercise 7.16** (p. 300): the electric-dipole *selection rules*. The physical setup (N&C §7.5.1)
is a matrix element `⟨ℓ₁,m₁| r̂ |ℓ₂,m₂⟩` of the position operator between hydrogenic orbital
wavefunctions; writing `r̂` in the `x̂–ŷ` plane in terms of the dipole spherical harmonics
`Y_{1,±1}` (N&C eq. 7.59), the angular part reduces to the **Gaunt-type overlap integral**.

## Content of this file — the azimuthal `m`-rule

* `sphHarmNorm`, `sphHarmRadial`, `sphHarm` — the spherical harmonic `Y_{ℓm}` (N&C 7.63/7.64).
* `dipoleOverlap` — the overlap integral (7.60), written as the iterated integral over `θ ∈ [0,π]`,
  `φ ∈ [0,2π]` with the solid-angle weight `sin θ` (so no Fubini/integrability lemmas are needed:
  the inner `φ`-integral already vanishes pointwise in `θ`).
* `dipoleOverlap_ne_zero_imp_delta_m` — the dipole corollary `m₂ − m₁ = ±1` for `m = ±1`, exactly as
  N&C state it.
-/

open scoped Real
open Polynomial

namespace AxQM.Concrete

/-- Normalization constant of the spherical harmonic `Y_{ℓm}`, N&C (7.63), with the `1/(2^ℓ ℓ!)`
of the Rodrigues formula (7.64) folded in (see `sphHarmRadial`). Uses the `|m|` convention. Its
value never enters the selection-rule proofs, which are invariant under nonzero rescaling. -/
noncomputable def sphHarmNorm (l : ℕ) (m : ℤ) : ℝ :=
  (-1) ^ m.natAbs * Real.sqrt ((2 * (l : ℝ) + 1) / (4 * Real.pi) *
      (((l - m.natAbs).factorial : ℝ) / ((l + m.natAbs).factorial : ℝ))) /
    (2 ^ l * (l.factorial : ℝ))

/-- The θ-radial part of the spherical harmonic `Y_{ℓm}`: N&C (7.63)/(7.64) written in `θ`. -/
noncomputable def sphHarmRadial (l : ℕ) (m : ℤ) (θ : ℝ) : ℝ :=
  sphHarmNorm l m * (Real.sin θ) ^ (m.natAbs) *
    (Polynomial.derivative^[l + m.natAbs] ((Polynomial.X ^ 2 - 1) ^ l)).eval (Real.cos θ)

/-- The spherical harmonic `Y_{ℓm}(θ,φ)` in separated form, N&C (7.63): a real θ-radial part times
the azimuthal phase `e^{imφ}`. -/
noncomputable def sphHarm (l : ℕ) (m : ℤ) (θ φ : ℝ) : ℂ :=
  (sphHarmRadial l m θ : ℂ) * Complex.exp (↑m * ↑φ * Complex.I)

/-- The electric-dipole overlap integral, N&C (7.60): `∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ` with the
solid-angle measure `dΩ = sin θ dθ dφ`, written as the iterated integral over `θ ∈ [0,π]`,
`φ ∈ [0,2π]`. The middle factor is the dipole harmonic `Y_{1,m}` (ℓ = 1). -/
noncomputable def dipoleOverlap (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi, (∫ φ in (0:ℝ)..(2 * Real.pi),
      (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ) * (Real.sin θ : ℂ)

/-- **Dipole azimuthal selection rule** (N&C Exercise 7.16, the `m₂ − m₁ = ±1` half). -/
theorem dipoleOverlap_ne_zero_imp_delta_m
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ} (hm : m = 1 ∨ m = -1)
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : m₂ - m₁ = 1 ∨ m₂ - m₁ = -1 := sorry

/-- **The `Δℓ = ±1` selection rule** (N&C Exercise 7.16, second stated rule). -/
theorem dipoleOverlap_ne_zero_imp_delta_l
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ}
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : (l₂ : ℤ) - l₁ = 1 ∨ (l₂ : ℤ) - l₁ = -1 := sorry

end AxQM.Concrete
