/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HarmonicOscillatorAmplitudeDamping
import AxQM.Concrete.PauliExponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Concrete: the beam-splitter propagator of a harmonic oscillator (N&C, Exercise 8.21, part 1)

This file begins the **derivation** of the
amplitude-damping operation elements of a harmonic oscillator (Nielsen & Chuang, Exercise 8.21, p.
381) from the interaction Hamiltonian `H = χ(a†b + b†a)` and the propagator `U = exp(-iHΔt)` — part
**(1)** of the exercise — rather than *positing* eq. 8.110 as a definition.
-/

namespace AxQM.Concrete

open scoped Matrix Matrix.Norms.Operator
open Matrix

/-- The **number-basis matrix of `a†b + b†a`** on the total-excitation sector `N = n`
(Nielsen & Chuang eq. 8.109, `H = χ(a†b + b†a)`), as an `(n+1) × (n+1)` complex matrix. The index
`j : Fin (n+1)` counts the quanta in the environment mode `b` (so the principal mode `a` holds
`n - j`); the tridiagonal off-diagonal entry `⟨j+1| Mₙ |j⟩ = √((j+1)(n-j))` is the exact
annihilation/creation matrix element `√(n-j)·√(j+1)` of `b†a` (its symmetric partner `⟨j| Mₙ |j+1⟩`
being that of `a†b`). The full Hamiltonian is `H = χ·Mₙ`. -/
noncomputable def fockBeamGen (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun r c =>
    if (r : ℕ) + 1 = (c : ℕ) then (Real.sqrt (((r : ℕ) + 1) * (n - (r : ℕ))) : ℂ)
    else if (c : ℕ) + 1 = (r : ℕ) then (Real.sqrt (((c : ℕ) + 1) * (n - (c : ℕ))) : ℂ)
    else 0

/-- The **sector propagator** `Uⁿ(θ) = exp(-iθMₙ)` — the restriction of `U = exp(-iHΔt)` to the
`n`-quantum sector, with `θ = χΔt` (`H = χMₙ`, so `-iHΔt = -iθMₙ`). This is a genuine finite matrix
exponential; the `k`-th operation element `Eₖ = ⟨k_b|U|0_b⟩` of eq. 8.110 reads its first column
off, sector by sector. -/
noncomputable def fockBeamProp (n : ℕ) (θ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  NormedSpace.exp ((-Complex.I * (θ : ℂ)) • fockBeamGen n)

/-- The **complex sector amplitude** `⟨n-k| Eₖ |n⟩ = √(C(n,k)) cosⁿ⁻ᵏθ (-i sinθ)ᵏ` of eq. 8.110
(`θ = χΔt`): the `(k)`-th component of the first column of `Uⁿ(θ)`, i.e. the amplitude for exactly
`k` of the `n` quanta to be transferred to the environment. Its modulus is the eq.-8.110 amplitude
`√(C(n,k)(1-γ)ⁿ⁻ᵏγᵏ)`; the phase `(-i)ᵏ` is the physical beam-splitter phase,
immaterial to the operation (operation elements are defined up to a phase). -/
noncomputable def fockBeamAmp (θ : ℝ) (n k : ℕ) : ℂ :=
  (Real.sqrt (n.choose k) : ℂ) * (Real.cos θ : ℂ) ^ (n - k) * (-Complex.I * (Real.sin θ : ℂ)) ^ k

/-- The **operation element** `Eₖ = ⟨k_b|U|0_b⟩` of eq. 8.110, assembled over all excitation-number
sectors into a single matrix `Matrix ℕ ℕ ℂ` on the principal oscillator's number space. Reading the
propagator `U = exp(-iHΔt)` sector by sector, `Eₖ` lowers `|n⟩` to `|n-k⟩` with the complex sector
amplitude `fockBeamAmp θ n k` (`fockBeamKraus_eq_prop_col`: this entry *is* the `k`-th component
`⟨k_b|Uⁿ(θ)|0_b⟩` of the sector propagator's first column, eq. 8.110 for all `n`). The `(r,c)`
entry is `fockBeamAmp θ c k` when `r + k = c` (row `c-k`, column `c`), and `0` otherwise; its
modulus is the eq.-8.110 real operation element `fockDampingKraus (sin²θ)` (`fockBeamKraus_norm`),
the per-column
phase `(-i)ᵏ` being immaterial to the operation. -/
noncomputable def fockBeamKraus (θ : ℝ) (k : ℕ) : Matrix ℕ ℕ ℂ :=
  fun r c => if r + k = c then fockBeamAmp θ c k else 0

/-- **The assembled operation element reads off the sector propagator's first column.** For `k ≤ n`
the amplitude `⟨n-k|Eₖ|n⟩` of the assembled `Eₖ` is exactly the `k`-th component of the first
column of the sector propagator `Uⁿ(θ) = exp(-iθMₙ)` — the environment overlap
`⟨k_b|Uⁿ(θ)|0_b⟩`: `fockBeamKraus θ k (n-k) n = fockBeamProp n θ ⟨k⟩ 0`. -/
theorem fockBeamKraus_eq_prop_col (θ : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    fockBeamKraus θ k (n - k) n = fockBeamProp n θ ⟨k, by omega⟩ 0 := sorry

/-- **Reconciliation with part (2)'s eq.-8.110 operation element.** The modulus of the operation
element `Eₖ` derived from `U = exp(-iHΔt)` is entrywise that of the real eq.-8.110 operation element
`fockDampingKraus (sin²θ)` (with loss probability `γ = sin²θ`):
`‖(Eₖ)_{rc}‖ = ‖(fockDampingKraus (sin²θ) k)_{rc}‖`. The derived elements thus coincide with the
eq.-8.110 elements up to the per-column phase `(-i)ᵏ`, immaterial to the operation — closing the
loop between the part-(1) derivation and part (2)'s modulus form. -/
theorem fockBeamKraus_norm (θ : ℝ) (k r c : ℕ) :
    ‖fockBeamKraus θ k r c‖ = ‖fockDampingKraus (Real.sin θ ^ 2) k r c‖ := sorry

/-- **Exercise 8.21, closing the loop. -/
theorem fockBeamKraus_completeness (θ : ℝ) (a b : ℕ) :
    (∑ᶠ k, ∑ᶠ j, (fockBeamKraus θ k)ᴴ a j * fockBeamKraus θ k j b)
      = (1 : Matrix ℕ ℕ ℂ) a b := sorry

end AxQM.Concrete
