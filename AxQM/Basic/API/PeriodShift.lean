/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.InverseQuantumFourierTransform
import AxQM.Basic.API.QuditMeasurement

/-!
# AxQM.Basic.API — the period-shift operator and its Fourier eigenstates

The development behind **Nielsen & Chuang Exercise 5.21** (Period-finding and phase
estimation). For a periodic function `f` with period `r` (`f(x+r) = f(x)`), whose `r` value states
`|f(0)⟩, …, |f(r-1)⟩` are distinct and orthonormal, one is given the **shift operator** `U_y`
(N&C's `U_y`) acting by `U_y|f(x)⟩ = |f(x+y)⟩`. Since the `r` value states are orthonormal and `U_y`
cyclically permutes them, they are canonically the computational basis of the `r`-level **period
register** `qudit r`, with `|f(x)⟩ = |x mod r⟩`; the shift is then the cyclic-shift gate
`|x⟩ ↦ |x+y⟩` on `Fin r` (`+` the modular addition of `Fin r`).

## Main declarations
* `periodShift r y` — the **shift operator** `U_y` of Exercise 5.21: `quditPerm` of the cyclic shift
  `Equiv.addRight y`, so `U_y|x⟩ = |x+y⟩`.
* `periodShift_hasEigenstate_qftInverseFourierImage` — **Exercise 5.21(1)**: the Fourier states
  `|f̂(ℓ)⟩ = F⁻¹|ℓ⟩` are eigenvectors of `U_y`, with eigenvalue `e^{2πiℓy/r}`.
* `quditBasis_eq_sum_qftInverseFourierImage` — **eq. (5.64)**, the inverse identity: a value state
  `|f(x₀)⟩ = |x₀⟩` is the equal-magnitude superposition `(1/√r) ∑_ℓ e^{2πiℓx₀/r} |f̂(ℓ)⟩` of *all*
  eigenstates — the content of Exercise 5.21(2).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **The single-register computational-basis permutation gate** `quditPerm σ` on `qudit d`, for a
permutation `σ : Equiv.Perm (Fin d)` of the basis labels: the unitary `Evolution` sending each
computational-basis state `|x⟩` to `|σ x⟩`. -/
def quditPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Evolution (qudit d) :=
  Evolution.ofLinearIsometryEquiv ((quditOrthonormalBasis d).equiv (quditOrthonormalBasis d) σ)

/-- **The period-shift operator** `U_y` of Nielsen & Chuang Exercise 5.21, on the period register
`qudit r`: the cyclic-shift gate `|x⟩ ↦ |x+y⟩` (`+` the modular addition of `Fin r`), realised as
`quditPerm` of the shift permutation `Equiv.addRight y`. It is `U_y|f(x)⟩ = |f(x+y)⟩` under the
identification `|f(x)⟩ = |x mod r⟩` of the value states with the computational basis. -/
def periodShift (r : ℕ) [NeZero r] (y : Fin r) : Evolution (qudit r) :=
  quditPerm (Equiv.addRight y)

/-- **Nielsen & Chuang, Exercise 5.21(1).** The Fourier states `|f̂(ℓ)⟩ = F⁻¹|ℓ⟩`
(`qftInverseFourierImage r ℓ`, N&C eq. 5.63) are the eigenvectors of the shift operator `U_y`
(`periodShift r y`), with eigenvalue `e^{2πiℓy/r}`:

`U_y |f̂(ℓ)⟩ = e^{2πiℓy/r} |f̂(ℓ)⟩`.
-/
theorem periodShift_hasEigenstate_qftInverseFourierImage (r : ℕ) [NeZero r] (y ℓ : Fin r) :
    (periodShift r y).HasEigenstate
      (Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r))
      (qftInverseFourierImage r ℓ) := sorry

/-- **Nielsen & Chuang, Exercise 5.21(2) / eq. (5.64).** A value state `|f(x₀)⟩ = |x₀⟩` is the
equal-magnitude superposition of *all* Fourier eigenstates `|f̂(ℓ)⟩`:

`|f(x₀)⟩ = (1/√r) ∑_ℓ e^{2πiℓx₀/r} |f̂(ℓ)⟩`.

This is the inverse of eq. (5.63): each `|f̂(ℓ)⟩` appears with amplitude of modulus `1/√r`.
-/
theorem quditBasis_eq_sum_qftInverseFourierImage (r : ℕ) [NeZero r] (x₀ : Fin r) :
    (quditBasis x₀).vec
      = ∑ ℓ : Fin r, ((Real.sqrt r : ℂ)⁻¹
          * Complex.exp (2 * Real.pi * Complex.I * ((x₀ : ℕ) * (ℓ : ℕ)) / r))
          • (qftInverseFourierImage r ℓ).vec := sorry

end AxQM
