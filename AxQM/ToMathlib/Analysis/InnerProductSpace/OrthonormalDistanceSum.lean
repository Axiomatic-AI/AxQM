/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Algebra.Order.Chebyshev

/-! # Sum of squared distances from a vector to an orthonormal family

For a normalized vector `ψ` and a finite orthonormal family `v : ι → E`, the total squared
distance from `ψ` to the members of the family is bounded below:
`∑ x, ‖ψ - v x‖² ≥ 2N - 2√N`, where `N = Fintype.card ι` is the number of vectors.

## Main results

* `Orthonormal.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq`: for a normalized `ψ`,
  `2N - 2√N ≤ ∑ x, ‖ψ - v x‖²`.
-/

@[expose] public section

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] {v : ι → E}

/-- **Nielsen & Chuang, Exercise 6.15** (eq. 6.53): for a normalized state vector `ψ`
(`‖ψ‖ = 1`) and a set of `N` orthonormal vectors `v x`,
`∑ x, ‖ψ - v x‖² ≥ 2N - 2√N`, where `N = Fintype.card ι`.
-/
theorem Orthonormal.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq
    (hv : Orthonormal 𝕜 v) {ψ : E} (hψ : ‖ψ‖ = 1) :
    2 * (Fintype.card ι : ℝ) - 2 * Real.sqrt (Fintype.card ι) ≤ ∑ x, ‖ψ - v x‖ ^ 2 := sorry
