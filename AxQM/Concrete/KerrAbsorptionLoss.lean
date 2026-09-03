/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.KerrTwoPhotonPhase
import AxQM.Concrete.DetunedRabiAbsorption

/-!
# Concrete: cross-phase-modulation loss (Nielsen & Chuang, Exercise 7.22)

Nielsen & Chuang §7.5.3 models the optical Kerr effect microscopically: two orthogonally polarised
photon modes `a`, `b` (each with at most one photon) interact with a single three-level atom, giving
a modified Jaynes–Cummings Hamiltonian whose relevant part is block diagonal (7.82),
`H = diag(H₀, H₁, H₂)`. The two-photon phase shift comes with a *loss*: the atom
can absorb a photon. Exercise 7.22 asks to compute this absorption probability for the two-photon
input `|110⟩` and **compare** it with the single-photon input `|100⟩`, as a function of
`δ, gₐ, g_b, t`.

## Main results

* `kerrSinglePhotonAbsorptionProb` — `1 - |⟨100|U|100⟩|² = detunedAbsorptionLoss δ gₐ t`
  `= gₐ²/(δ²+gₐ²)·sin²(√(δ²+gₐ²)·t)`.
* `kerrTwoPhotonAbsorptionProb` — `1 - |⟨110|U|110⟩|² = detunedAbsorptionLoss δ √(gₐ²+g_b²) t`,
  the same profile at the **effective coupling** `√(gₐ²+g_b²)`.
-/

namespace AxQM.Concrete

open NormedSpace Matrix

noncomputable section

open scoped Matrix.Norms.Operator

/-- **The detuned-block absorption/loss profile** (Nielsen & Chuang eq. 7.79). -/
def detunedAbsorptionLoss (δ g t : ℝ) : ℝ :=
  g ^ 2 / (δ ^ 2 + g ^ 2) * Real.sin (Real.sqrt (δ ^ 2 + g ^ 2) * t) ^ 2

/-- The **single-excitation block `H₁`** (Nielsen & Chuang eq. 7.84) of the modified
Jaynes–Cummings Hamiltonian, as the block-diagonal direct sum
`detunedBlock δ gₐ ⊕ detunedBlock δ g_b` of the two single-mode detuned blocks. In the basis
`|100⟩, |001⟩, |010⟩, |002⟩` this is exactly
`!![-δ, gₐ, 0, 0; gₐ, δ, 0, 0; 0, 0, -δ, g_b; 0, 0, g_b, δ]` (7.84): mode `a` couples
`|100⟩ ↔ |001⟩` with strength `gₐ`, mode `b` couples `|010⟩ ↔ |002⟩` with strength `g_b`, and the
two modes decouple. We index the sector as `(position, mode) : Fin 2 × Fin 2`, so the
single-photon mode-`a` input state `|100⟩` is `(0, 0)` (position `0`, mode `0`). -/
def kerrBlockOne (δ ga gb : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal ![detunedBlock δ ga, detunedBlock δ gb]

/-- **Exercise 7.22, single-photon loss.** The probability that the single photon `|100⟩` is
absorbed by the atom, `1 - |⟨100|U|100⟩|²` with `U = exp(-iHt)` and `H` as in (7.82), is the
detuned-block absorption profile at coupling `gₐ`:
`1 - |⟨100|U|100⟩|² = detunedAbsorptionLoss δ gₐ t = gₐ²/(δ²+gₐ²)·sin²(√(δ²+gₐ²)·t)`. -/
theorem kerrSinglePhotonAbsorptionProb (δ ga gb t : ℝ) (hga : 0 < δ ^ 2 + ga ^ 2) :
    1 - Complex.normSq ((exp (-(Complex.I * (t : ℂ)) • kerrBlockOne δ ga gb)) (0, 0) (0, 0))
      = detunedAbsorptionLoss δ ga t := sorry

/-- **Exercise 7.22, two-photon loss.** The probability that a photon is absorbed from the
two-photon input `|110⟩`, `1 - |⟨110|U|110⟩|²` with `U = exp(-iHt)` and `H` as in (7.82), is the
detuned-block absorption profile at the **effective coupling** `√(gₐ²+g_b²)`. -/
theorem kerrTwoPhotonAbsorptionProb (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    1 - Complex.normSq ((exp (-(Complex.I * (t : ℂ)) • kerrBlockTwo δ ga gb)) 0 0)
      = detunedAbsorptionLoss δ (Real.sqrt (ga ^ 2 + gb ^ 2)) t := sorry

end

end AxQM.Concrete
