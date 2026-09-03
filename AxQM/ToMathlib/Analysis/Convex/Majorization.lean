/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.Rearrangement

/-!
# Majorization of real vectors

Majorization is an order on real vectors capturing the idea that one vector is more spread out
(less "disordered") than another.  For `x y : ι → ℝ` on a finite index type `ι` we say `x` is
*majorized* by `y`, `Majorize x y`, when the sum of the `k` largest entries of `x` is at most that
of `y` for every `k`, and the two total sums agree.

## Main definitions

* `largestKSum x k`: the maximum of `∑ i ∈ s, x i` over `k`-element subsets `s`.
* `Majorize x y`: `x` is majorized by `y`.
* `tailSum x t`: the tail/cut function `∑ i, max (x i - t) 0`.

## Main statements

* `convex_setOf_majorize`: the set of vectors majorized by a fixed `y` is convex
  (Nielsen–Chuang, Exercise 12.18).
* `majorize_iff_exists_sum_perm`: **Nielsen–Chuang, Proposition 12.11** — `Majorize x y` holds iff
  `x = ∑ⱼ pⱼ Pⱼ y` for a probability distribution `pⱼ` and permutation matrices `Pⱼ`.
* `majorize_iff_forall_tailSum`: **Nielsen–Chuang, Exercise 12.17** — `Majorize x y` holds iff
  `∀ t, tailSum x t ≤ tailSum y t` together with equality of the total sums.

## Tags

majorization, doubly stochastic, Schur
-/

public section

open Finset Function Matrix
open scoped BigOperators

variable {ι : Type*}

/-- `largestKSum x k` is the largest sum of `k` entries of `x`: the supremum of `∑ i ∈ s, x i` over
`k`-element subsets `s` of the index type.  It equals `0` when `k` exceeds the dimension, since then
no such subset exists. -/
noncomputable def largestKSum (x : ι → ℝ) (k : ℕ) : ℝ :=
  ⨆ s : {s : Finset ι // s.card = k}, ∑ i ∈ (s : Finset ι), x i

/-- `x` is *majorized* by `y` (written `x ≺ y` in the literature): the sum of the `k` largest
entries of `x` is at most the sum of the `k` largest entries of `y` for every `k`, and the total
sums agree.  This is recorded compactly by requiring that every subset sum of `x` is bounded by the
largest equal-sized subset sum of `y`, together with equality of the total sums. -/
def Majorize [Fintype ι] (x y : ι → ℝ) : Prop :=
  (∑ i, x i = ∑ i, y i) ∧ ∀ s : Finset ι, ∑ i ∈ s, x i ≤ largestKSum y s.card

variable [Fintype ι]

/-- The set of vectors majorized by a fixed `y` is convex (Nielsen–Chuang, Exercise 12.18). -/
lemma convex_setOf_majorize (y : ι → ℝ) : Convex ℝ {x | Majorize x y} := sorry

/-- **Nielsen–Chuang, Proposition 12.11.**  `x` is majorized by `y` if and only if `x` is a convex
combination of permutation matrices applied to `y`. -/
theorem majorize_iff_exists_sum_perm [DecidableEq ι] {x y : ι → ℝ} :
    Majorize x y ↔ ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      x = ∑ σ : Equiv.Perm ι, w σ • (σ.permMatrix ℝ *ᵥ y) := sorry

/-- `tailSum x t = ∑ i, max (x i - t) 0` is the *tail* (or *cut*) function of `x` at threshold `t`:
the sum of the positive parts of the shifted entries `x i - t`. -/
noncomputable def tailSum (x : ι → ℝ) (t : ℝ) : ℝ := ∑ i, max (x i - t) 0

/-- **Nielsen–Chuang, Exercise 12.17.**  `x` is majorized by `y` if and only if the tail functions
are pointwise ordered, `tailSum x t ≤ tailSum y t` for every threshold `t`, together with equality
of the total sums.
-/
theorem majorize_iff_forall_tailSum {x y : ι → ℝ} :
    Majorize x y ↔ (∀ t : ℝ, tailSum x t ≤ tailSum y t) ∧ ∑ i, x i = ∑ i, y i := sorry

/-- **Nielsen–Chuang, Exercise 12.19.** -/
theorem majorize_tail_update_of_antitone {n : ℕ} {x y : Fin (n + 1) → ℝ} (hx : Antitone x)
    (hy : Antitone y) (hxy : Majorize x y) {p : Fin (n + 1)} (hp : p ≠ 0) {t : ℝ}
    (hhi : x 0 ≤ y (p - 1)) (hx0 : x 0 = t * y 0 + (1 - t) * y p) :
    Majorize (Fin.tail x) (Fin.tail (Function.update y p ((1 - t) * y 0 + t * y p))) := sorry
