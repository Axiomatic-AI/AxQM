/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # The exponential of a scalar multiple of a sum of commuting elements

In a Banach algebra, the exponential of a sum of pairwise-commuting elements whose summands are
scaled by a common scalar — most notably `-i t`, giving the time-evolution operator `e^{-iHt}` of a
Hamiltonian `H = ∑ₖ Hₖ`.
-/

@[expose] public section

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- **Nielsen & Chuang, Exercise 4.47.** For a Hamiltonian written as a sum `H = ∑ₖ Hₖ` of
pairwise-commuting summands, the time-evolution operator factors over the summands:
`exp (-(i t) • ∑ₖ Hₖ) = ∏ₖ exp (-(i t) • Hₖ)`,
i.e. `e^{-iHt} = e^{-iH₁t} ⋯ e^{-iH_L t}`. Since the factors commute the product is taken as a
`Finset.noncommProd` and is independent of the order of the summands. -/
theorem exp_neg_I_mul_smul_sum_of_commute [NormedAlgebra ℂ 𝔸] {ι : Type*}
    (s : Finset ι) (t : ℝ) (H : ι → 𝔸)
    (h : (s : Set ι).Pairwise (Function.onFun Commute H)) :
    exp (-(Complex.I * t) • ∑ k ∈ s, H k) =
      s.noncommProd (fun k => exp (-(Complex.I * t) • H k))
        fun _ hi _ hj hij => (((h hi hj hij).smul_left _).smul_right _).exp := sorry

end NormedSpace
