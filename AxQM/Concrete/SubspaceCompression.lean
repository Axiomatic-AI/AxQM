/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Concrete: compressing a matrix to an invariant coordinate subspace (matrix level)
-/

namespace AxQM.Concrete

open Matrix

variable {α β : Type*}

/-- **`N` preserves the coordinate subspace `range ι` on the right.** Every column of `N` indexed by
a range basis element `ι s` is supported on `range ι`: `N r (ι s) = 0` whenever `r ∉ range ι`.
Equivalently, `N` maps each basis vector `e_{ι s}` of the subspace back into the subspace. -/
def PreservesRange (ι : α → β) (N : Matrix β β ℂ) : Prop :=
  ∀ (s : α) (r : β), r ∉ Set.range ι → N r (ι s) = 0

/-- **The range-preserving matrices form a submonoid** of `Matrix β β ℂ`. -/
def compressionInvariant [Fintype β] [DecidableEq β] (ι : α → β) :
    Submonoid (Matrix β β ℂ) where
  carrier := {N | PreservesRange ι N}
  one_mem' := fun s r hr => by
    rw [Matrix.one_apply, if_neg (fun h => hr ⟨s, h.symm⟩)]
  mul_mem' := fun {M N} hM hN s r hr => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ Set.range ι
    · obtain ⟨u, rfl⟩ := ht
      rw [hM u r hr, zero_mul]
    · rw [hN s t ht, mul_zero]

/-- **The compression of `M` to the coordinate subspace `range ι`** — the submatrix
`M.submatrix ι ι`, keeping only the rows and columns indexed by `range ι`. When `ι` picks out the
data basis indices of a register whose ancillas are held `|1⟩`, `compress ι M` is the action of `M`
on the data register. -/
def compress (ι : α → β) (M : Matrix β β ℂ) : Matrix α α ℂ :=
  M.submatrix ι ι

end AxQM.Concrete
