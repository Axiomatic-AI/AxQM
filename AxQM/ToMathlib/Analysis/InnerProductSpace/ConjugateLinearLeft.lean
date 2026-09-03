/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Conjugate-linearity of the inner product in the first argument (finite sums)

Mathlib fixes the sesquilinear convention in which the inner product `⟪·, ·⟫` is
*conjugate-linear* in its first argument and linear in its second. This file states that
convention for a finite linear combination `∑ᵢ λᵢ • wᵢ` in the first slot.
-/

@[expose] public section

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inner product is **conjugate-linear in its first argument**: for a finite linear combination
`∑ i ∈ s, l i • w i`, `⟪∑ i ∈ s, l i • w i, v⟫ = ∑ i ∈ s, conj (l i) * ⟪w i, v⟫`.
-/
theorem sum_smul_inner (s : Finset ι) (l : ι → 𝕜) (w : ι → E) (v : E) :
    inner 𝕜 (∑ i ∈ s, l i • w i) v = ∑ i ∈ s, (starRingEnd 𝕜) (l i) * inner 𝕜 (w i) v := sorry
