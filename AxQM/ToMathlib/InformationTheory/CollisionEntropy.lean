/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Collision probability and collision entropy

For a finite type `ι` and a function `p : ι → ℝ` (interpreted as a probability mass function when
`p i ∈ [0, 1]` and `∑ i, p i = 1`), the **collision probability** is `∑ᵢ (p i)²` and the
**collision entropy** (Rényi entropy of order 2) is `-log₂` of the collision probability.

## Main definitions

- `Real.collisionProb : (ι → ℝ) → ℝ`
- `Real.collisionEntropy : (ι → ℝ) → ℝ`
-/

@[expose] public section

namespace Real

variable {ι : Type*} [Fintype ι]

/-- The **collision probability** of `p : ι → ℝ`: `∑ i, (p i) ^ 2`. For a probability mass function
this is `Pr[X = X'] = ∑ₓ p(x)²`, the probability that two independent draws collide. -/
noncomputable def collisionProb (p : ι → ℝ) : ℝ := ∑ i, p i ^ 2

/-- The **collision entropy** (Rényi entropy of order 2) of `p : ι → ℝ`, in bits:
`Hc(p) = -log₂ (∑ᵢ (p i)²)`. -/
noncomputable def collisionEntropy (p : ι → ℝ) : ℝ := -Real.logb 2 (collisionProb p)

end Real
