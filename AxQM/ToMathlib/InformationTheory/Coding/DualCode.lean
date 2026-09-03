/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The dual of a classical linear code

The **dual code** `C⊥` of a linear code `C ⊆ Kⁿ` is the set of all words orthogonal to every
codeword under the standard dot product `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, §10.4.1, p. 449).

## Main definitions

* `stdBilin K ι`: the standard dot-product bilinear form `⟨x, y⟩ = x ⬝ᵥ y` on `ι → K`.
* `LinearCode.dual C`: the dual code `C⊥`, the orthogonal complement of `C` with respect to
  `stdBilin`.
* `LinearCode.IsSelfOrthogonal C`: `C` is **weakly self-dual** (self-orthogonal), `C ⊆ C⊥`
  (N&C §10.4.1, p. 449).

## Main results

* `LinearCode.mem_dual_iff`: `y ∈ C⊥` iff `x ⬝ᵥ y = 0` for every codeword `x ∈ C`.
* `LinearCode.finrank_dual`: `dim C⊥ = n - dim C`, where `n = #ι` is the block length. An `[n, k]`
  code thus has an `[n, n - k]` dual (N&C §10.4.1).
-/

open Matrix

@[expose] public section

/-- The standard **dot-product bilinear form** `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` on the word space `ι → K`, given
by `Matrix.toBilin'` of the identity matrix. -/
noncomputable def stdBilin (K ι : Type*) [Field K] [Fintype ι] [DecidableEq ι] :
    LinearMap.BilinForm K (ι → K) :=
  Matrix.toBilin' (1 : Matrix ι ι K)

@[simp] theorem stdBilin_apply {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] (x y : ι → K) :
    (stdBilin K ι x) y = x ⬝ᵥ y := by
  rw [stdBilin, Matrix.toBilin'_apply', Matrix.one_mulVec]

/-- The standard dot-product form is nondegenerate. -/
theorem stdBilin_nondegenerate {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    (stdBilin K ι).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' 1 (by
    rw [Matrix.det_one]; exact one_ne_zero)

namespace LinearCode

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The **dual code** `C⊥` of a linear code `C`: the set of words orthogonal to every codeword under
the standard dot product (Nielsen & Chuang, §10.4.1, p. 449). -/
noncomputable def dual (C : LinearCode K ι) : LinearCode K ι :=
  (stdBilin K ι).orthogonal C

/-- A word lies in the dual code `C⊥` exactly when it is orthogonal to every codeword. -/
theorem mem_dual_iff {C : LinearCode K ι} {y : ι → K} :
    y ∈ dual C ↔ ∀ x ∈ C, x ⬝ᵥ y = 0 := by
  simp only [dual, LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.isOrtho_def,
    stdBilin_apply]

/-- **Dimension of the dual code**: `dim C⊥ = n - dim C`, where `n = #ι` is the block length. An
`[n, k]` code has an `[n, n - k]` dual (Nielsen & Chuang, §10.4.1). -/
theorem finrank_dual (C : LinearCode K ι) :
    Module.finrank K (dual C) = Fintype.card ι - Module.finrank K C := by
  rw [dual, LinearMap.BilinForm.finrank_orthogonal stdBilin_nondegenerate, Module.finrank_pi]

/-- A linear code is **weakly self-dual** (self-orthogonal) when it is contained in its dual,
`C ⊆ C⊥` (Nielsen & Chuang, §10.4.1, p. 449). -/
def IsSelfOrthogonal (C : LinearCode K ι) : Prop := C ≤ dual C

end LinearCode

end
