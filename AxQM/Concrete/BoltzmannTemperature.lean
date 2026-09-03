/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Concrete: the two-level Boltzmann distribution and its temperature (N&C Exercise 8.25)

Real analysis about the **Boltzmann (Gibbs) occupation probabilities** of a two-level system and
the temperature they encode.

## Contents

* `boltzmannGround`, `boltzmannExcited` — the occupation probabilities `p₀`, `p₁` (the Boltzmann
  distribution of the exercise).
* `boltzmannTemperature` — **the answer**: the temperature `T = (E₁-E₀)/(k_B ln(p/(1-p)))`.
* `boltzmannGround_boltzmannTemperature`, `boltzmannExcited_boltzmannTemperature` — at that
  temperature the populations are exactly `p` and `1 - p`, i.e. it reproduces the stationary state
  `ρ∞ = diag(p, 1-p)`.
* `boltzmannTemperature_unique` — and it is the *unique* (nonzero) temperature that does so, so
  `boltzmannTemperature` genuinely "describes the state `ρ∞`".
-/

open Real

noncomputable section

namespace AxQM.Concrete

variable (E₀ E₁ kB T p : ℝ)

/-- **Boltzmann ground-state occupation** `p₀ = e^{-E₀/(k_B T)} / Z` of a two-level system with
energies `E₀` (state `|0⟩`) and `E₁` (state `|1⟩`) in thermal equilibrium at temperature `T`, with
partition function `Z = e^{-E₀/(k_B T)} + e^{-E₁/(k_B T)}` and Boltzmann constant `k_B` (N&C
Exercise 8.25). -/
def boltzmannGround : ℝ :=
  Real.exp (-E₀ / (kB * T)) / (Real.exp (-E₀ / (kB * T)) + Real.exp (-E₁ / (kB * T)))

/-- **Boltzmann excited-state occupation** `p₁ = e^{-E₁/(k_B T)} / Z` (N&C Exercise 8.25). -/
def boltzmannExcited : ℝ :=
  Real.exp (-E₁ / (kB * T)) / (Real.exp (-E₀ / (kB * T)) + Real.exp (-E₁ / (kB * T)))

/-- **The temperature describing the stationary state `ρ∞ = diag(p, 1-p)`** (N&C Exercise 8.25, the
answer): `T = (E₁ - E₀) / (k_B ln(p/(1-p)))`. -/
def boltzmannTemperature : ℝ := (E₁ - E₀) / (kB * Real.log (p / (1 - p)))

/-- **Exercise 8.25 (ground population).** At `T = boltzmannTemperature`, the Boltzmann ground-state
occupation equals `p` — the `|0⟩` population of the stationary state `ρ∞ = diag(p, 1-p)`. Needs the
populations strictly between `0` and `1` (`0 < p < 1`), unequal (`p ≠ 1/2`), a nonzero energy gap
(`E₀ ≠ E₁`), and `k_B ≠ 0`. -/
theorem boltzmannGround_boltzmannTemperature
    (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) (hE : E₀ ≠ E₁) (hkB : kB ≠ 0) :
    boltzmannGround E₀ E₁ kB (boltzmannTemperature E₀ E₁ kB p) = p := sorry

/-- **Exercise 8.25 (excited population).** At `T = boltzmannTemperature`, the Boltzmann
excited-state occupation equals `1 - p` — the `|1⟩` population of `ρ∞ = diag(p, 1-p)`. -/
theorem boltzmannExcited_boltzmannTemperature
    (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) (hE : E₀ ≠ E₁) (hkB : kB ≠ 0) :
    boltzmannExcited E₀ E₁ kB (boltzmannTemperature E₀ E₁ kB p) = 1 - p := sorry

/-- **Exercise 8.25 (uniqueness).** `boltzmannTemperature` is the *only* nonzero temperature at
which the Boltzmann ground occupation equals `p`: if `boltzmannGround E₀ E₁ kB T = p` for some
`T ≠ 0` (with `0 < p < 1`, `p ≠ 1/2`, `k_B ≠ 0`), then `T = boltzmannTemperature E₀ E₁ kB p`. -/
theorem boltzmannTemperature_unique
    (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) (hkB : kB ≠ 0) (hT : T ≠ 0)
    (hEq : boltzmannGround E₀ E₁ kB T = p) :
    T = boltzmannTemperature E₀ E₁ kB p := sorry

end AxQM.Concrete

end
