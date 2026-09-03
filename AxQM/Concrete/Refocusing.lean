/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationConjugation

/-!
# Concrete: refocusing a single spin's free precession (Nielsen & Chuang, Exercise 7.38)

Nielsen & Chuang, §7.7.3 ("Refocusing"), introduces the `180°` NMR pulse `R²ₓ₁` as the square of
the `90°` rotation `Rₓ₁ = exp(−iπX/4)` (eq. 7.149) and states the *refocusing identity* (eq. 7.150).

## Main declarations
* `zEvolution a t = exp(−i a Z t)` — the free-precession propagator of a single spin under the
  Hamiltonian `H = a Z` (N&C §7.7.3), as a genuine `2 × 2` matrix exponential.
* `pauliX_mul_zEvolution_mul_pauliX` — the **refocusing identity's physical content**,
  `X · e^{−iaZt} · X = e^{+iaZt}` (here `e^{+iaZt} = zEvolution a (−t)`, i.e. refocusing *reverses*
  the time evolution). This is (7.150) with the `180°` pulse identified with the Pauli `X` (a
  `180°` `x`-pulse is `X` up to a global phase).
* `refocusPulse = rotX π` — the `180°` `x`-pulse `R²ₓ₁`, the square of the `90°` pulse
  `Rₓ₁ = rotX (π/2)` (eq. 7.149).
* `refocusPulse_mul_zEvolution_mul_refocusPulse` — the **literal** identity (7.150) with the
  *exact* exponential pulse `R²ₓ₁ = −iX`: `R²ₓ₁ · e^{−iaZt} · R²ₓ₁ = −e^{+iaZt}`.
-/

namespace AxQM.Concrete

open Matrix Complex NormedSpace

/-- The **free-precession propagator** `e^{−iaZt}` of a single spin under the Hamiltonian `H = a Z`
(Nielsen & Chuang, §7.7.3), as the `2 × 2` matrix exponential `exp(−i (a t) Z)`. The accumulated
phase depends only on the product `a t`; `zEvolution a (−t) = e^{+iaZt}` is the time-reversed
propagator. -/
noncomputable def zEvolution (a t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  exp ((((-(a * t) : ℝ) : ℂ) * Complex.I) • pauliZ)

/-- **Refocusing identity (physical content), Nielsen & Chuang eq. 7.150.** Conjugating the
free-precession propagator by the Pauli `X` reverses the evolution: `X · e^{−iaZt} · X =
e^{+iaZt}` (`= zEvolution a (−t)`). -/
theorem pauliX_mul_zEvolution_mul_pauliX (a t : ℝ) :
    pauliX * zEvolution a t * pauliX = zEvolution a (-t) := sorry

/-- The **`180°` `x`-pulse** `R²ₓ₁ = exp(−iπX/2)`, the square of the `90°` rotation
`Rₓ₁ = exp(−iπX/4)` (Nielsen & Chuang, eq. 7.149), realized as `rotX π`. -/
noncomputable def refocusPulse : Matrix (Fin 2) (Fin 2) ℂ := rotX Real.pi

/-- **Refocusing identity, literal form (Nielsen & Chuang eq. 7.150), exact exponential pulse.**
`R²ₓ₁ · e^{−iaZt} · R²ₓ₁ = −e^{+iaZt}` (`= −zEvolution a (−t)`): (7.150) as printed holds up to
the physically-irrelevant global phase `−1`. -/
theorem refocusPulse_mul_zEvolution_mul_refocusPulse (a t : ℝ) :
    refocusPulse * zEvolution a t * refocusPulse = -zEvolution a (-t) := sorry

end AxQM.Concrete
