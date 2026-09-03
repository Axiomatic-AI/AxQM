/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.RingTheory.Finiteness.Basic

/-!

# Some finiteness results of `PiTensorProduct`

Finiteness results for `PiTensorProduct`: a finite subset of `⨂[R] i, M i` lies in the image of
the tensor product of a family of finitely generated submodules.

## Tags

tensor product, pi tensor product, finitely generated
-/

@[expose] public section

open Submodule

open scoped TensorProduct

namespace PiTensorProduct

variable {ι : Type*} {R : Type*} {M : ι → Type*} [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Monotonicity of the range of `mapIncl` in the family of submodules. -/
lemma range_mapIncl_mono {p q : Π i, Submodule R (M i)} (h : ∀ i, p i ≤ q i) :
    LinearMap.range (mapIncl p) ≤ LinearMap.range (mapIncl q) := by
  have hcomp : mapIncl p = mapIncl q ∘ₗ map (fun i ↦ Submodule.inclusion (h i)) := by
    ext m; simp [mapIncl, Submodule.inclusion]
  rw [hcomp]
  exact LinearMap.range_comp_le_range _ _

/-- For a finite subset `s` of `⨂[R] i, M i`, there is a family of finitely generated submodules
`M' i ≤ M i` such that `s` is contained in the image of `⨂[R] i, M' i` in `⨂[R] i, M i`.

In particular, every element of a `PiTensorProduct` lies in the `PiTensorProduct` of some
finitely generated submodules. -/
theorem exists_finite_submodule_of_setFinite (s : Set (⨂[R] i, M i)) (hs : s.Finite) :
    ∃ M' : Π i, Submodule R (M i), (∀ i, Module.Finite R (M' i)) ∧
      s ⊆ LinearMap.range (mapIncl M') := by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨fun _ ↦ ⊥, fun _ ↦ fg_bot, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
    obtain ⟨M', hM', h⟩ := ih
    refine PiTensorProduct.induction_on a (fun r f ↦ ?_) (fun x y hx hy ↦ ?_)
    · refine ⟨fun i ↦ M' i ⊔ Submodule.span R {f i},
        fun i ↦ (hM' i).sup (fg_span_singleton _),
        Set.insert_subset ?_ fun z hz ↦ ?_⟩
      · refine ⟨r • tprod R fun i ↦ ⟨f i, mem_sup_right (mem_span_singleton_self _)⟩, ?_⟩
        simp [mapIncl]
      · exact range_mapIncl_mono (fun _ ↦ le_sup_left) (h hz)
    · obtain ⟨M₁', hM₁', h₁⟩ := hx
      obtain ⟨M₂', hM₂', h₂⟩ := hy
      refine ⟨fun i ↦ M₁' i ⊔ M₂' i,
        fun i ↦ (hM₁' i).sup (hM₂' i),
        Set.insert_subset (add_mem ?_ ?_) fun z hz ↦ ?_⟩
      · exact range_mapIncl_mono (fun _ ↦ le_sup_left) (h₁ (Set.mem_insert x s))
      · exact range_mapIncl_mono (fun _ ↦ le_sup_right) (h₂ (Set.mem_insert y s))
      · exact range_mapIncl_mono (fun _ ↦ le_sup_left) (h₁ (Set.subset_insert x s hz))

end PiTensorProduct
