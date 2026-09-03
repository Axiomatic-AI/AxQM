/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import AxQM.ToMathlib.RingTheory.MvPolynomial.Multilinear

/-!
# Concrete: the OR polynomial `1 - ∏ₖ (1 - Xₖ)` (Nielsen & Chuang, Exercise 6.19)

*(N&C p. 273.)*

The polynomial `1 − (1 − X₀)(1 − X₁) ⋯ (1 − X_{N-1})` represents the OR function.

## Declarations

* `Represents p F` — N&C's representation predicate: `p` evaluated at every Boolean point
  (encoding `true ↦ 1`, `false ↦ 0`) returns the `{0, 1}`-encoded value of `F`.
* `orFun` — the OR Boolean function `b ↦ (∃ k, bₖ = true)`.
* `orPoly` — the polynomial `1 - ∏ᵢ (1 - Xᵢ)`.
* `orPoly_represents_orFun` — **Exercise 6.19 itself**: `orPoly` represents `orFun`.
-/

namespace AxQM.Concrete

open MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- **Representation of a Boolean function by a polynomial** (Nielsen & Chuang, §6.7). A polynomial
`p` *represents* the Boolean function `F : (σ → Bool) → Bool` when, evaluated at every Boolean point
`X ∈ {0, 1}ˢ` (encoding `true ↦ 1`, `false ↦ 0`), it returns the `{0, 1}`-encoded value `F(X)`:
`p(X) = F(X)` for all `X`. This is N&C's notion of a polynomial representing a Boolean function. -/
def Represents (p : MvPolynomial σ R) (F : (σ → Bool) → Bool) : Prop :=
  ∀ b : σ → Bool, eval (fun i => if b i then (1 : R) else 0) p = if F b then 1 else 0

/-- **The OR Boolean function**: `true` iff at least one coordinate is `true`, i.e. N&C's
`X₀ ∨ X₁ ∨ ⋯ ∨ X_{N-1}`. -/
def orFun [Fintype σ] (b : σ → Bool) : Bool := decide (∃ i, b i = true)

/-- **The OR polynomial** `P(X) = 1 − (1 − X₀)(1 − X₁) ⋯ (1 − X_{N-1})` of Nielsen & Chuang,
Exercise 6.19: the explicit multilinear polynomial claimed to represent the OR function. -/
noncomputable def orPoly [Fintype σ] : MvPolynomial σ R := 1 - ∏ i, (1 - X i)

/-- **Nielsen & Chuang, Exercise 6.19.** The polynomial `P(X) = 1 − ∏ₖ (1 − Xₖ)` represents the
OR function. -/
theorem orPoly_represents_orFun [Fintype σ] :
    Represents (orPoly : MvPolynomial σ R) orFun := sorry

end AxQM.Concrete
