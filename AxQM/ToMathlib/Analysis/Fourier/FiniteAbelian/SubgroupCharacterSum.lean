/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Character sums over subgroups and their factorization over products

Let `A` be a finite additive abelian group and `ψ : AddChar A R` a character valued in an integral
domain `R` of characteristic zero (e.g. `ℂ`). This file studies the sum of `ψ` over a subgroup
`K ≤ A` and, when `A = ∏ᵢ Aᵢ` is a finite product with `K = ∏ᵢ Kᵢ` a product of subgroups, its
factorization across the factors.

## Main statements

* `sum_pi_subgroup_zmod_prod` — the sum over `K = ∏ᵢ Kᵢ` factorizes as `∏ᵢ (∑_{hᵢ ∈ Kᵢ} ψ(ℓᵢhᵢ))`;
* `sum_pi_subgroup_zmod_eq_natCard_iff` — that sum equals `|K|` iff each factor equals `|Kᵢ|`.
-/

@[expose] public section

open scoped BigOperators

namespace AddChar

section Pi

variable {ι : Type*} [Fintype ι]
  {A : ι → Type*} [∀ i, AddCommGroup (A i)]

section CommMonoid

variable {R : Type*} [CommMonoid R]

instance instDecidablePredMemPiUniv (K : ∀ i, AddSubgroup (A i)) [∀ i, DecidablePred (· ∈ K i)] :
    DecidablePred (· ∈ AddSubgroup.pi (Set.univ : Set ι) K) := fun f =>
  decidable_of_iff (∀ i, f i ∈ K i) (by simp [AddSubgroup.mem_pi])

end CommMonoid

variable [DecidableEq ι] [∀ i, Fintype (A i)]

end Pi

section ZMod

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)]

/-- **The character sum over a product of subgroups factorizes.** For `K = ∏ᵢ Kᵢ ≤ ∏ᵢ ℤ_{nᵢ}` and
`ℓ : ∀ i, ZMod (n i)`, `∑_{h ∈ K} ∏ᵢ e^{2πi ℓᵢhᵢ/nᵢ} = ∏ᵢ ∑_{hᵢ ∈ Kᵢ} e^{2πi ℓᵢhᵢ/nᵢ}`. -/
theorem sum_pi_subgroup_zmod_prod (K : ∀ i, AddSubgroup (ZMod (n i)))
    [∀ i, DecidablePred (· ∈ K i)] (ℓ : ∀ i, ZMod (n i)) :
    ∑ h : ↥(AddSubgroup.pi (Set.univ) K),
        ∏ i, ZMod.stdAddChar (ℓ i * (h : ∀ i, ZMod (n i)) i)
      = ∏ i, ∑ h : ↥(K i), ZMod.stdAddChar (ℓ i * (h : ZMod (n i))) := sorry

/-- **The (5.77) condition over `G = ∏ᵢ ℤ_{nᵢ}` holds iff it holds factorwise** (Nielsen & Chuang,
Exercise 5.26). With the standard characters `ZMod.stdAddChar (ℓᵢ · hᵢ) = e^{2πi ℓᵢ hᵢ / nᵢ}`, the
character sum over the hidden subgroup `K = ∏ᵢ K_{pᵢ}` attains its maximum `|K|` **iff each
per-factor sum attains `|K_{pᵢ}|`**. -/
theorem sum_pi_subgroup_zmod_eq_natCard_iff (K : ∀ i, AddSubgroup (ZMod (n i)))
    [∀ i, DecidablePred (· ∈ K i)] (ℓ : ∀ i, ZMod (n i)) :
    (∑ h : ↥(AddSubgroup.pi (Set.univ) K),
          ∏ i, ZMod.stdAddChar (ℓ i * (h : ∀ i, ZMod (n i)) i)
        = Fintype.card ↥(AddSubgroup.pi (Set.univ) K))
      ↔ ∀ i, ∑ h : ↥(K i), ZMod.stdAddChar (ℓ i * (h : ZMod (n i)))
          = Fintype.card ↥(K i) := sorry

end ZMod

end AddChar
