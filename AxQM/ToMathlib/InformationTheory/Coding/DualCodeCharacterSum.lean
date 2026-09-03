/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.DualCode
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The character sum of a binary linear code and its dual

For a binary linear code `C ⊆ (ι → ZMod 2)` and a word `x`, the **character sum**
`∑_{y ∈ C} (-1)^{x · y}` (with `x · y` the standard dot product in `ZMod 2` and `(-1)^{·}` read as a
real number) is a dual-code indicator: it equals the number of codewords `|C|` when `x` is
orthogonal to every codeword — i.e. `x ∈ C⊥` — and vanishes otherwise (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 10.25, p. 450).

## Main results

* `neg_one_pow_zmod2_val_add`: the sign map `a ↦ (-1)^{a.val}` on `ZMod 2` is an
  additive-to-multiplicative homomorphism, `(-1)^{(a+b).val} = (-1)^{a.val} · (-1)^{b.val}`.
* `LinearCode.sum_neg_one_pow_dotProduct`: the indicator form
  `∑_{y ∈ C} (-1)^{x·y} = if x ∈ C⊥ then |C| else 0`.
* `LinearCode.sum_neg_one_pow_dotProduct_complex`: the same indicator identity with the signs taken
  in `ℂ` (with an explicit `[DecidablePred (· ∈ C)]` binder).
-/

open Matrix

@[expose] public section

/-- On `ZMod 2` the **sign map** `a ↦ (-1)^{a.val}` is an additive-to-multiplicative homomorphism:
`(-1)^{(a+b).val} = (-1)^{a.val} · (-1)^{b.val}` in any ring `R`. -/
theorem neg_one_pow_zmod2_val_add {R : Type*} [Ring R] (a b : ZMod 2) :
    (-1 : R) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

namespace LinearCode

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **Character sum of a binary linear code** (Nielsen & Chuang, Exercise 10.25, p. 450). For a
binary linear code `C` and a word `x`,
`∑_{y ∈ C} (-1)^{x·y} = |C|` if `x ∈ C⊥` and `= 0` otherwise. -/
theorem sum_neg_one_pow_dotProduct (C : LinearCode (ZMod 2) ι) (x : ι → ZMod 2) :
    ∑ y : ↥C, (-1 : ℝ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val
      = if x ∈ C.dual then (Nat.card ↥C : ℝ) else 0 := sorry

open Classical in
/-- **Complex character sum of a binary linear code**: `∑_{y ∈ C} (-1)^{x·y} = |C|` if `x ∈ C⊥` and
`= 0` otherwise, with the signs taken in `ℂ`. -/
theorem sum_neg_one_pow_dotProduct_complex (C : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C)]
    (x : ι → ZMod 2) :
    ∑ y : ↥C, (-1 : ℂ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val
      = if x ∈ C.dual then (Nat.card ↥C : ℂ) else 0 := by
  by_cases hx : x ∈ C.dual
  · rw [if_pos hx]
    have hone : ∀ y : ↥C, (-1 : ℂ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val = 1 := fun y => by
      have hz : x ⬝ᵥ (y : ι → ZMod 2) = 0 := by
        rw [dotProduct_comm]; exact mem_dual_iff.1 hx _ y.2
      rw [hz, ZMod.val_zero, pow_zero]
    rw [Finset.sum_congr rfl (fun y _ => hone y)]
    simp [Finset.card_univ, Nat.card_eq_fintype_card]
  · rw [if_neg hx]
    rw [mem_dual_iff] at hx
    push Not at hx
    obtain ⟨z, hz, hznz⟩ := hx
    set y₀ : ↥C := ⟨z, hz⟩ with hy0
    set f : ↥C → ℂ := fun y => (-1 : ℂ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val with hf
    have hxy0 : x ⬝ᵥ (y₀ : ι → ZMod 2) = 1 := by
      rw [dotProduct_comm]; exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hznz
    have hf0 : f y₀ = -1 := by
      have hval : (x ⬝ᵥ (y₀ : ι → ZMod 2)).val = 1 := by rw [hxy0]; decide
      simp only [hf, hval, pow_one]
    have hom : ∀ a b : ↥C, f (a + b) = f a * f b := fun a b => by
      simp only [hf, Submodule.coe_add, dotProduct_add]
      exact neg_one_pow_zmod2_val_add _ _
    set S := ∑ y : ↥C, f y with hS
    have key : f y₀ * S = S := by
      rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft y₀) f]
      exact Finset.sum_congr rfl fun y _ => (hom y₀ y).symm
    rw [hf0] at key
    linear_combination (-1 / 2 : ℂ) * key

end LinearCode

end
