/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the two-photon Kerr phase shift (Nielsen & Chuang, Exercise 7.21)

Nielsen & Chuang §7.5.3 models the optical Kerr effect microscopically: two orthogonally polarised
photon modes `a`, `b` (each with at most one photon) interact with a single three-level atom, giving
a modified Jaynes–Cummings Hamiltonian (7.81). In the total-excitation basis the relevant part of
the Hamiltonian is block diagonal (7.82), `H = diag(H₀, H₁, H₂)`.

## Main declarations
* `kerrRabiFreq` — the generalised Rabi frequency `Ω' = √(δ² + gₐ² + g_b²)`.
* `kerrBlockTwo`, `kerrBlockZero` — the `H₂` (7.85) and `H₀` (7.83) blocks (over `ℂ`).
* `kerrTwoPhotonPhase_arg` — Exercise 7.21, eq. (7.86):
  `ϕ_ab = arg[e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)]`.
-/

open scoped Matrix Matrix.Norms.Operator
open Matrix

noncomputable section

namespace AxQM.Concrete

/-- The **generalised Rabi frequency** `Ω' = √(δ² + gₐ² + g_b²)` of the modified Jaynes–Cummings
model (Nielsen & Chuang §7.5.3, eq. 7.86): the level splitting of the two-excitation sector. -/
def kerrRabiFreq (δ ga gb : ℝ) : ℝ := Real.sqrt (δ ^ 2 + ga ^ 2 + gb ^ 2)

/-- The **`H₂` block** (Nielsen & Chuang eq. 7.85) of the modified Jaynes–Cummings Hamiltonian on
the two-excitation sector, in the basis `|110⟩, |011⟩, |102⟩`:
`H₂ = !![-δ, gₐ, g_b; gₐ, δ, 0; g_b, 0, δ]`. Real detuning `δ` and couplings `gₐ, g_b`, as a complex
`3 × 3` matrix (so its matrix exponential is available). -/
def kerrBlockTwo (δ ga gb : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(δ : ℂ), (ga : ℂ), (gb : ℂ); (ga : ℂ), (δ : ℂ), 0; (gb : ℂ), 0, (δ : ℂ)]

/-- The **`H₀` block** (Nielsen & Chuang eq. 7.83) on the vacuum `|000⟩`: the `1 × 1` matrix `[-δ]`,
whose exponential gives the reference amplitude `⟨000|U|000⟩ = e^{-iδt}`. -/
def kerrBlockZero (δ : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := !![-(δ : ℂ)]

/-- **Exercise 7.21 (Nielsen & Chuang eq. 7.86).** The two-photon Kerr phase shift
`ϕ_ab = arg⟨110|U|110⟩ − arg⟨000|U|000⟩` (`U = exp(itH)`) equals
`arg[e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)]`, with `Ω' = √(δ² + gₐ² + g_b²)`. Here `ϕ_ab` is realised
as the argument of the amplitude ratio `⟨110|U|110⟩ / ⟨000|U|000⟩` (`arg` of a quotient being the
difference of arguments, mod `2π` — the physical phase's inherent ambiguity). -/
theorem kerrTwoPhotonPhase_arg (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    Complex.arg ((NormedSpace.exp ((Complex.I * t) • kerrBlockTwo δ ga gb)) 0 0
        / (NormedSpace.exp ((Complex.I * t) • kerrBlockZero δ)) 0 0)
      = Complex.arg (Complex.exp (Complex.I * δ * t)
        * ((Real.cos (kerrRabiFreq δ ga gb * t) : ℂ)
          - ((δ : ℂ) / (kerrRabiFreq δ ga gb : ℂ)) * (Real.sin (kerrRabiFreq δ ga gb * t) : ℂ)
            * Complex.I)) := sorry

end AxQM.Concrete

end
