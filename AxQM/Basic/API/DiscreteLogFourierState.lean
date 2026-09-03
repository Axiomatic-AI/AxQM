/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.OrderFindingEigenstate
import AxQM.ToMathlib.Analysis.SpecialFunctions.Complex.PeriodicDFT

/-!
# AxQM.Basic.API — the discrete-log Fourier state `|f̂(ℓ₁,ℓ₂)⟩` (N&C Ex 5.22)

The development behind **Nielsen & Chuang Exercise 5.22** (§5.4.2, discrete
logarithms, p. 239). Fix a modulus `N`, a unit `a` of `ZMod N` (the base `a` of `b = aˢ`) of
multiplicative order `r = orderOf a`, and the discrete logarithm `s`.

## Main declarations
* `dlogFourierDoubleSum a s ℓ₁ ℓ₂` — the (un-normalized) double sum
  `∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩`, the left-hand side of (5.72).
* `dlogFourierSingleSum a ℓ₂` — the (un-normalized) single sum
  `∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩`, N&C's `√r·|f̂(ℓ₂)⟩` of eq. (5.70).
* `dlogFourierDoubleSum_of_modEq` — **eq. (5.72), on support**: if `ℓ₁ ≡ s·ℓ₂ (mod r)` then
  `DoubleSum = r • SingleSum`.
* `dlogFourierDoubleSum_eq_zero_of_not_modEq` — **the constraint**: otherwise `DoubleSum = 0`.
-/

noncomputable section

namespace AxQM

open Finset Complex
open scoped Real
open AxQM.Concrete (orbitIndex orbitIndex_mod)

variable {N : ℕ} [NeZero N] (a : (ZMod N)ˣ)

/-- **The discrete-log function-value state** `|f(x₁,x₂)⟩ = |a^{s·x₁+x₂} mod N⟩` of N&C §5.4.2, as a
computational-basis `PureState` of `qudit N`. Its label is the order-finding orbit index of the
combined exponent `s·x₁ + x₂` (`b = aˢ`, so `f(x₁,x₂) = bˣ¹aˣ² = a^{s·x₁+x₂}`). -/
def dlogBasisState (s x₁ x₂ : ℕ) : PureState (qudit N) :=
  quditBasis (orbitIndex a (s * x₁ + x₂))

/-- **The double sum of N&C eq. (5.72)** (un-normalized): the two-dimensional Fourier transform
`∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩` over the fundamental domain, `r = orderOf a`. -/
def dlogFourierDoubleSum (s ℓ₁ ℓ₂ : ℕ) : (qudit N).space :=
  ∑ x₁ ∈ range (orderOf a), ∑ x₂ ∈ range (orderOf a),
    exp (-(2 * (π : ℂ) * I * ((ℓ₁ : ℂ) * (x₁ : ℂ) + (ℓ₂ : ℂ) * (x₂ : ℂ)) / (orderOf a : ℂ)))
      • (dlogBasisState a s x₁ x₂).vec

/-- **The single sum of N&C eq. (5.70)** (un-normalized): the one-dimensional Fourier transform
`∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩` over the coset representatives; equals `√r·|f̂(ℓ₂)⟩`. -/
def dlogFourierSingleSum (ℓ₂ : ℕ) : (qudit N).space :=
  ∑ j ∈ range (orderOf a),
    exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (j : ℂ) / (orderOf a : ℂ)))
      • (quditBasis (orbitIndex a j)).vec

/-- **N&C Exercise 5.22, eq. (5.72) on support.** When the constraint `ℓ₁ ≡ s·ℓ₂ (mod r)` holds, the
double sum collapses to `r` times the single sum over the coset representatives:

  `∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩ = r · ∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩`.
-/
theorem dlogFourierDoubleSum_of_modEq (s ℓ₁ ℓ₂ : ℕ)
    (h : ℓ₁ ≡ s * ℓ₂ [MOD orderOf a]) :
    dlogFourierDoubleSum a s ℓ₁ ℓ₂ = (orderOf a : ℂ) • dlogFourierSingleSum a ℓ₂ := sorry

/-- **N&C Exercise 5.22, the constraint.** When `ℓ₁ ≢ s·ℓ₂ (mod r)` the amplitude of the double sum
`r ∣ (s·ℓ₂−ℓ₁)`. -/
theorem dlogFourierDoubleSum_eq_zero_of_not_modEq (s ℓ₁ ℓ₂ : ℕ)
    (h : ¬ ℓ₁ ≡ s * ℓ₂ [MOD orderOf a]) :
    dlogFourierDoubleSum a s ℓ₁ ℓ₂ = 0 := sorry

end AxQM
