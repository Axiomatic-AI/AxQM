/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# Concrete: Rabi oscillations — exponentiating the single-excitation Jaynes–Cummings Hamiltonian
(Nielsen & Chuang, Exercise 7.18)

The time-evolution operator `exp(-iHt)` of the single-excitation Jaynes–Cummings Hamiltonian
(7.76), in the closed Rabi-oscillation form (7.77).
-/

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace AxQM.Concrete

/-- The **Rabi frequency** `Ω = √(g² + δ²)` (Nielsen & Chuang §7.5.3, below eq. 7.77):
the angular frequency at which the atom and field exchange a quantum of energy. -/
noncomputable def rabiFrequency (δ g : ℝ) : ℝ := Real.sqrt (g ^ 2 + δ ^ 2)

/-- The **single-excitation Jaynes–Cummings Hamiltonian** (Nielsen & Chuang eq. 7.76), the
restriction of (7.71) to `span{|00⟩, |01⟩, |10⟩}` (basis ordered `|field, atom⟩`, `N` neglected):
`H = -!![δ,0,0; 0,δ,g; 0,g,-δ]`, with detuning `δ` and coupling `g`. -/
noncomputable def rabiHamiltonian (δ g : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(δ : ℂ), 0, 0; 0, -(δ : ℂ), -(g : ℂ); 0, -(g : ℂ), (δ : ℂ)]

/-- The **Rabi-oscillation unitary** `U = exp(-iHt)` (the corrected Nielsen & Chuang eq. 7.77):
`U = e^{iδt} |00⟩⟨00| + (cos Ωt + i(δ/Ω) sin Ωt) |01⟩⟨01| + (cos Ωt - i(δ/Ω) sin Ωt) |10⟩⟨10|
     + i(g/Ω) sin Ωt (|01⟩⟨10| + |10⟩⟨01|)`,
with `Ω = √(g²+δ²)` the Rabi frequency. (The printed equation carries two sign typos.)

The `|00⟩⟨00|` entry is written in the factored form `e^{it(δ-Ω)}·(cos Ωt + i sin Ωt)`, which
equals N&C's `e^{iδt}`. -/
noncomputable def rabiUnitary (δ g t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.exp (Complex.I * (t : ℂ) * ((δ : ℂ) - ((rabiFrequency δ g : ℝ) : ℂ)))
       * ((Real.cos (rabiFrequency δ g * t) : ℂ)
           + (Real.sin (rabiFrequency δ g * t) : ℂ) * Complex.I), 0, 0;
     0,
       (Real.cos (rabiFrequency δ g * t) : ℂ)
         + Complex.I * ((δ / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ),
       Complex.I * ((g / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ);
     0,
       Complex.I * ((g / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ),
       (Real.cos (rabiFrequency δ g * t) : ℂ)
         - Complex.I * ((δ / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ)]

/-- **Nielsen & Chuang, Exercise 7.18 (Rabi oscillations).** The time-evolution operator
`exp(-iHt)` of the single-excitation Jaynes–Cummings Hamiltonian (7.76) is the Rabi-oscillation
unitary (7.77):
`exp((-i t) • rabiHamiltonian δ g) = rabiUnitary δ g t`,
for nonzero Rabi frequency `Ω = √(g²+δ²) ≠ 0`, which (7.77) divides by. -/
theorem exp_neg_I_smul_rabiHamiltonian (δ g t : ℝ) (hΩ : rabiFrequency δ g ≠ 0) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • rabiHamiltonian δ g) = rabiUnitary δ g t := sorry

/-- The `|00⟩` phase collapses to N&C's `e^{iδt}`: the factored `|00⟩` entry
`e^{it(δ-Ω)}·(cos Ωt + i sin Ωt)` of `rabiUnitary` equals `e^{iδt}`. This is the "fixed
phase" of the `|00⟩` mode that N&C notes may be neglected. -/
theorem rabiUnitary_apply_zero_zero (δ g t : ℝ) :
    rabiUnitary δ g t 0 0 = Complex.exp (Complex.I * ((δ * t : ℝ) : ℂ)) := sorry

end AxQM.Concrete
