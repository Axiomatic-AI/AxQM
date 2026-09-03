/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Concrete: the spontaneous emission rate `γ_rad` (Nielsen & Chuang, Exercise 7.29)

Nielsen & Chuang §7.6.3 (p. 316) derives the spontaneous emission rate of an atom coupled to the
electromagnetic vacuum through the Jaynes–Cummings interaction (7.109). To lowest order in the
coupling, an excited atom coupled to a single optical mode of frequency `ω` decays with probability
(N&C 7.110)
`p_decay(ω, t) = g²(ω) · 4 sin²(½(ω-ω₀)t) / (ω-ω₀)²`,
where `ℏω₀` is the atomic transition energy and the (frequency-dependent) coupling is (7.111)
`g²(ω) = ω₀² |⟨0|μ|1⟩|² / (2 ℏ ω ε₀ c²)`.
An atom in free space interacts with *all* optical modes; summing over polarisations and solid
angle (`8π/3`) and the three-dimensional mode density (`ω²/(2πc)³`) and integrating over modes gives
the total decay probability `P(t)` (N&C 7.113). **Exercise 7.29** asks to (1) evaluate this mode
integral and (2) differentiate the result in `t` to obtain the emission rate (N&C 7.112)
`γ_rad = ω₀³ |⟨0|μ|1⟩|² / (3π ℏ ε₀ c⁵)`.

## Contents

* `couplingSq` — the atom–field coupling `g²(ω)` (N&C 7.111).
* `pDecay` — the single-mode decay probability `p_decay` (N&C 7.110), in terms of `g²`.
* `gammaRad` — the target emission rate `γ_rad` (N&C 7.112).
* `spontaneousDecayProb` — the resonance-approximated mode integral `P(t)` (N&C 7.113).
* `spontaneousDecayProb_eq_gammaRad_mul` — **step 1** (physical `t ≥ 0`): `P(t) = γ_rad · t`.
* `deriv_spontaneousDecayProb_eq_gammaRad` — **step 2** (`t > 0`): `dP/dt = γ_rad` (N&C 7.112).
-/

open MeasureTheory Real

namespace SpontaneousEmission

/-- The atom–field coupling strength squared `g²(ω)` (Nielsen & Chuang 7.111). -/
noncomputable def couplingSq (ω₀ ħ ε₀ c μ ω : ℝ) : ℝ :=
  ω₀ ^ 2 * μ ^ 2 / (2 * ħ * ω * ε₀ * c ^ 2)

/-- The single-mode spontaneous decay probability `p_decay` (Nielsen & Chuang 7.110):
`p_decay = g² · 4 sin²(½(ω-ω₀)t) / (ω-ω₀)²`, to lowest order in the coupling, for an atom coupled to
one empty optical mode of frequency `ω`. The first argument is the coupling `g²` of (7.111). -/
noncomputable def pDecay (gSq ω ω₀ t : ℝ) : ℝ :=
  gSq * (4 * Real.sin ((ω - ω₀) * t / 2) ^ 2) / (ω - ω₀) ^ 2

/-- The spontaneous emission rate `γ_rad` (Nielsen & Chuang 7.112):
`γ_rad = ω₀³ |⟨0|μ|1⟩|² / (3π ℏ ε₀ c⁵)`. -/
noncomputable def gammaRad (ω₀ ħ ε₀ c μ : ℝ) : ℝ :=
  ω₀ ^ 3 * μ ^ 2 / (3 * Real.pi * ħ * ε₀ * c ^ 5)

/-- The total spontaneous-decay probability `P(t)` from summing over all optical modes (Nielsen &
Chuang 7.113), in the resonance/peak approximation: the mode-density weight `ω²` and the
coupling `g²(ω)` — slowly varying across the sharp resonance — are evaluated at the peak `ω =
ω₀` and pulled out, and the frequency integral of the sharply-peaked lineshape runs over all of
`ℝ`. Explicitly, `P(t) = 1/(2πc)³ · 8π/3 · ∫_ℝ ω₀² · p_decay(g²(ω₀), ω, ω₀, t) dω`. -/
noncomputable def spontaneousDecayProb (ω₀ ħ ε₀ c μ t : ℝ) : ℝ :=
  (1 / (2 * Real.pi * c) ^ 3) * (8 * Real.pi / 3) *
    ∫ ω : ℝ, ω₀ ^ 2 * pDecay (couplingSq ω₀ ħ ε₀ c μ ω₀) ω ω₀ t

/-- **Exercise 7.29, step 1.** For physical (non-negative) time, the resonance-approximated mode
integral is linear in `t` with slope the emission rate:
`P(t) = γ_rad · t`  (Nielsen & Chuang 7.113 → the coefficient of 7.112). -/
theorem spontaneousDecayProb_eq_gammaRad_mul (ω₀ ħ ε₀ c μ t : ℝ)
    (hω₀ : ω₀ ≠ 0) (hħ : ħ ≠ 0) (hε₀ : ε₀ ≠ 0) (hc : c ≠ 0) (ht : 0 ≤ t) :
    spontaneousDecayProb ω₀ ħ ε₀ c μ t = gammaRad ω₀ ħ ε₀ c μ * t := sorry

/-- **Exercise 7.29, step 2.** The time derivative of the resonance-approximated mode integral is
the spontaneous emission rate `dP/dt = γ_rad` (Nielsen & Chuang 7.112) — the probability of decay
per unit time. -/
theorem deriv_spontaneousDecayProb_eq_gammaRad (ω₀ ħ ε₀ c μ t : ℝ)
    (hω₀ : ω₀ ≠ 0) (hħ : ħ ≠ 0) (hε₀ : ε₀ ≠ 0) (hc : c ≠ 0) (ht : 0 < t) :
    deriv (fun s => spontaneousDecayProb ω₀ ħ ε₀ c μ s) t = gammaRad ω₀ ħ ε₀ c μ := sorry

end SpontaneousEmission
