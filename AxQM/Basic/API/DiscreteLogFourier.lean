/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.DiscreteLogFourierState

/-!
# AxQM.Basic.API — inverting the discrete-log Fourier double sum (N&C Ex 5.23)

The development behind **Nielsen & Chuang Exercise 5.23** (§5.4.2, the discrete
logarithm problem, p. 239). It builds directly on the Exercise 5.22
development: fix a modulus `N`, a unit `a` of `ZMod N` (the base, `b = aˢ`) of
multiplicative order `r = orderOf a`, and the discrete logarithm `s`.

## Main declarations
* `dlogFourierState a s ℓ₁ ℓ₂` — the eq.-(5.70)+(5.71) normalized Fourier state `|f̂(ℓ₁,ℓ₂)⟩`
  (`orderEigenstate a ℓ₂` on the support `ℓ₁ ≡ s·ℓ₂ (mod r)`, else `0`).
* `dlogFourierDoubleSum_eq_smul_dlogFourierState` — the bridge `DoubleSum = r√r · dlogFourierState`
  identifying it as the normalized Exercise-5.22 two-dimensional Fourier transform.
* `dlogInverseFourierSum a s x₁ x₂` — the inverse-Fourier double sum (5.73).
* `dlogInverseFourierSum_eq_smul_dlogBasisState` — **the reconstruction:** the double sum is
  `(1/√r)·|f(x₁,x₂)⟩`.
* `dlogForwardFourierSum a s x₁ x₂`, `dlogForwardFourierSum_eq_smul_reflected` — the literal
  printed-`−` sum and its honest value, the reflected state, exhibiting the sign misprint.
-/

noncomputable section

namespace AxQM

open Finset Complex
open scoped Real
open AxQM.Concrete (orbitIndex orbitIndex_mod)

variable {N : ℕ} [NeZero N] (a : (ZMod N)ˣ)

/-- **The discrete-log Fourier state `|f̂(ℓ₁,ℓ₂)⟩` of N&C eq. (5.70)+(5.71).** In the value register
`qudit N` it is the normalized single-`ℓ₂` Fourier state `orderEigenstate a ℓ₂ =
(1/√r) ∑_j e^{−2πiℓ₂j/r}|f(0,j)⟩` **on its support** `ℓ₁ ≡ s·ℓ₂ (mod r)`, and `0` off it (eq. 5.71:
"otherwise the amplitude … is nearly zero"; Exercise 5.22's
`dlogFourierDoubleSum_eq_zero_of_not_modEq`). The condition is written as the residue equality
`(ℓ₁ : ℕ) % r = (s·ℓ₂) % r`, i.e. `ℓ₁ ≡ s·ℓ₂ (mod r)`. -/
def dlogFourierState (s : ℕ) (ℓ₁ ℓ₂ : Fin (orderOf a)) : (qudit N).space :=
  if (ℓ₁ : ℕ) % orderOf a = (s * (ℓ₂ : ℕ)) % orderOf a then (orderEigenstate a ℓ₂).vec else 0

/-- **Bridge to Exercise 5.22.** The (un-normalized) two-dimensional Fourier transform of `f`
(`dlogFourierDoubleSum`) is `r·√r` times the normalized Fourier state `dlogFourierState`. This
pins `dlogFourierState` as the genuine normalized eq.-(5.70) state, not an `ℓ₁`-independent
surrogate. -/
theorem dlogFourierDoubleSum_eq_smul_dlogFourierState (s : ℕ) (ℓ₁ ℓ₂ : Fin (orderOf a)) :
    dlogFourierDoubleSum a s (ℓ₁ : ℕ) (ℓ₂ : ℕ)
      = ((orderOf a : ℂ) * (Real.sqrt (orderOf a) : ℂ)) • dlogFourierState a s ℓ₁ ℓ₂ := sorry

/-- **The inverse-Fourier double sum (5.73)** of Nielsen & Chuang Exercise 5.23, `(1/r) ∑_{ℓ₁,ℓ₂<r}
e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩`, as a vector of the value register `(qudit N).space`. -/
def dlogInverseFourierSum (s x₁ x₂ : ℕ) : (qudit N).space :=
  (orderOf a : ℂ)⁻¹ • ∑ ℓ₁ : Fin (orderOf a), ∑ ℓ₂ : Fin (orderOf a),
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((ℓ₁ : ℕ) * (x₁ : ℂ) + (ℓ₂ : ℕ) * (x₂ : ℂ)) / (orderOf a : ℂ))
      • dlogFourierState a s ℓ₁ ℓ₂

/-- **Nielsen & Chuang Exercise 5.23 — the reconstruction.** Computing the inverse-Fourier double
sum (5.73) using (5.70), the result is the value state `f(x₁,x₂)`, up to the section's `1/√r`
normalization:

  `(1/r) ∑_{ℓ₁,ℓ₂<r} e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩ = (1/√r) |f(x₁,x₂)⟩`. -/
theorem dlogInverseFourierSum_eq_smul_dlogBasisState (s x₁ x₂ : ℕ) :
    dlogInverseFourierSum a s x₁ x₂
      = (Real.sqrt (orderOf a) : ℂ)⁻¹ • (dlogBasisState a s x₁ x₂).vec := sorry

/-- **The literal printed inverse-Fourier double sum (5.73)**, with the forward sign `e^{−2πi(…)}`
exactly as printed on p. 239. -/
def dlogForwardFourierSum (s x₁ x₂ : ℕ) : (qudit N).space :=
  (orderOf a : ℂ)⁻¹ • ∑ ℓ₁ : Fin (orderOf a), ∑ ℓ₂ : Fin (orderOf a),
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
        ((ℓ₁ : ℕ) * (x₁ : ℂ) + (ℓ₂ : ℕ) * (x₂ : ℂ)) / (orderOf a : ℂ)))
      • dlogFourierState a s ℓ₁ ℓ₂

/-- **The printed sign gives the reflected state.** With N&C's printed `e^{−2πi(…)}` (the *forward*
sign, not the inverse transform's `+` of eq. 5.64), the double sum reconstructs the reflected value
state `|a^{−(s·x₁+x₂)}⟩ = |f(−x₁,−x₂)⟩` (the `|a^{(r−1)m}⟩` of the collapse), up to `1/√r` —
**not** `|f(x₁,x₂)⟩`. This is why the inverse-transform sign `+` (`dlogInverseFourierSum`) is the
faithful one; the printed `−` is a sign misprint, exhibited here rather than silently corrected. -/
theorem dlogForwardFourierSum_eq_smul_reflected (s x₁ x₂ : ℕ) :
    dlogForwardFourierSum a s x₁ x₂
      = (Real.sqrt (orderOf a) : ℂ)⁻¹
          • (quditBasis (orbitIndex a ((orderOf a - 1) * (s * x₁ + x₂)))).vec := sorry

end AxQM
