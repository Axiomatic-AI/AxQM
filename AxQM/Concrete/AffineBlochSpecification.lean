/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic

/-!
# Concrete: specifying an affine Bloch-sphere map needs at least four points

This file supplies the mathematical content behind **Nielsen & Chuang, Exercise 8.33 (p. 394)**.

## The answer

* `four_le_card_of_specifiesAffineBloch` — **the exercise:** any set of Bloch points that
  *specifies* the affine map (two affine maps agreeing on all of them are equal) has at least four
  points.
-/

namespace AxQM.Concrete

open Matrix Module

/-- A finite set `s` of Bloch points **specifies** affine Bloch-sphere maps if any two affine maps
`r ↦ M r + c` that transform every point of `s` identically are the same map. This is the formal
reading of Nielsen & Chuang's question whether the images of a set of Bloch points pin down a
single-qubit operation: the point-transform data determines `(M, c)`. -/
def SpecifiesAffineBloch (s : Finset (Fin 3 → ℝ)) : Prop :=
  ∀ (M₁ M₂ : Matrix (Fin 3) (Fin 3) ℝ) (c₁ c₂ : Fin 3 → ℝ),
    (∀ r ∈ s, M₁.mulVec r + c₁ = M₂.mulVec r + c₂) → M₁ = M₂ ∧ c₁ = c₂

/-- **Nielsen & Chuang, Exercise 8.33.** Any set of Bloch points that completely specifies a single
qubit operation via its point-transforms `r ↦ M r + c` must contain **at least four points**. -/
theorem four_le_card_of_specifiesAffineBloch {s : Finset (Fin 3 → ℝ)}
    (h : SpecifiesAffineBloch s) : 4 ≤ s.card := sorry

end AxQM.Concrete
