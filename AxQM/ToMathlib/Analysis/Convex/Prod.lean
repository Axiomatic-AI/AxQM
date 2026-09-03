/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Real.Basic

/-!
# Concavity on a product of convex sets, and its converse failure

A function `f : E × F → β` that is concave on a product set `s ×ˢ t` (i.e. *jointly*
concave in its two arguments) is concave in each argument separately, with the other held
fixed. This file records that slice, and the fact that the converse fails: separate
concavity in each argument does **not** imply joint concavity.

## Main results

* `ConcaveOn.slice_left` — if `f` is concave on `s ×ˢ t`, then for each fixed `b ∈ t` the
  map `a ↦ f (a, b)` is concave on `s`.
* `mulPair` — the product `(x, y) ↦ x * y` on `ℝ × ℝ`.
* `mulPair_concaveOn_left`, `mulPair_concaveOn_right` — `mulPair` is (affine, hence) concave
  in each argument separately.
* `mulPair_not_concaveOn` — `mulPair` is **not** jointly concave: it is the standard example
  of a function concave in each input yet not jointly concave.
-/

@[expose] public section

open Set

section Slice

variable {𝕜 E F β : Type*}
  [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid β] [PartialOrder β]
  [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]
  {s : Set E} {t : Set F} {f : E × F → β}

/-- **Joint concavity implies concavity in the first argument.** If `f` is concave on the
product `s ×ˢ t`, then for any fixed `b ∈ t`, the function `a ↦ f (a, b)` is concave on `s`. -/
theorem ConcaveOn.slice_left (hf : ConcaveOn 𝕜 (s ×ˢ t) f) {b : F} (hb : b ∈ t) :
    ConcaveOn 𝕜 s (fun a => f (a, b)) := sorry

end Slice

section Counterexample

/-- The product function `(x, y) ↦ x * y` on `ℝ × ℝ`. It is the standard example of a
function that is concave (indeed affine) in each argument separately, yet not jointly
concave. -/
def mulPair (p : ℝ × ℝ) : ℝ := p.1 * p.2

/-- `mulPair` is concave in its first argument (with the second held fixed). -/
theorem mulPair_concaveOn_left (b : ℝ) : ConcaveOn ℝ Set.univ (fun a => mulPair (a, b)) := sorry

/-- `mulPair` is concave in its second argument (with the first held fixed). -/
theorem mulPair_concaveOn_right (a : ℝ) : ConcaveOn ℝ Set.univ (fun b => mulPair (a, b)) := sorry

/-- `mulPair` is **not** jointly concave: a function concave in each input separately but not
jointly concave (N&C Exercise 11.23). -/
theorem mulPair_not_concaveOn : ¬ ConcaveOn ℝ (Set.univ : Set (ℝ × ℝ)) mulPair := sorry

end Counterexample
