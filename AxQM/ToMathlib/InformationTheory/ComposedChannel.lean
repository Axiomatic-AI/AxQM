/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.BinaryChannels

/-!
# Series composition of discrete memoryless channels and its capacity

For channels `q₁ : ι → κ → ℝ` and `q₂ : κ → μ → ℝ`, feeding the output of `q₁` into `q₂` gives the
**series composition** `N₂ ∘ N₁`, the channel `Real.channelComp q₁ q₂ : ι → μ → ℝ` with conditional
law `p(z | x) = ∑_y q₁(y | x) q₂(z | y)` (matrix product of the two transition matrices). This file
proves the capacity bound of **Nielsen & Chuang, Exercise 12.10** (p. 553):

## Main declarations

* `Real.channelComp` — the series composition `q₁; q₂` of two channels.
* `Real.channelCapacity_channelComp_le_min` — **Exercise 12.10 (bound)**:
  `C(N₂ ∘ N₁) ≤ min (C(N₁)) (C(N₂))`.
* `Real.channelCapacity_channelComp_bscChannel_lt_min` — **Exercise 12.10 (strict example)**: for
  `0 < p < 1/2` the bound is *strict* for `N₁ = N₂ = bscChannel p`.
-/

@[expose] public section

namespace Real

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- The **series composition** `N₂ ∘ N₁` of two discrete memoryless channels `q₁ : ι → κ → ℝ` and
`q₂ : κ → μ → ℝ`: feeding the output of `q₁` into `q₂` gives the conditional law
`p(z | x) = ∑_y q₁(y | x) q₂(z | y)` (the matrix product of the transition matrices). -/
noncomputable def channelComp (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ) : ι → μ → ℝ :=
  fun x z => ∑ y, q₁ x y * q₂ y z

/-- **Nielsen & Chuang, Exercise 12.10.** The capacity of the series composition `N₂ ∘ N₁` of two
channels is at most the minimum of the two individual capacities,
`C(N₂ ∘ N₁) ≤ min (C(N₁)) (C(N₂))`. This is the classical data processing inequality at the level of
capacities: composing channels can only lose information. -/
theorem channelCapacity_channelComp_le_min [Nonempty ι] [Nonempty κ] [Nonempty μ]
    {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ} (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) :
    channelCapacity (channelComp q₁ q₂) ≤ min (channelCapacity q₁) (channelCapacity q₂) := sorry

/-- **Nielsen & Chuang, Exercise 12.10 (strict example).** The capacity bound
`channelCapacity_channelComp_le_min` can be *strict*. -/
theorem channelCapacity_channelComp_bscChannel_lt_min {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    channelCapacity (channelComp (bscChannel p) (bscChannel p))
      < min (channelCapacity (bscChannel p)) (channelCapacity (bscChannel p)) := sorry

end Real
