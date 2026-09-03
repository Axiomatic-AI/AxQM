/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A positive operator on a complex inner product space is Hermitian

Let `E` be a complex inner product space. An operator `T : E →ₗ[ℂ] E` is *positive* in the sense of
Nielsen & Chuang (Exercise 2.24) when the quadratic form `⟪T x, x⟫` is a real, non-negative number
for every `x`. Over `ℂ` these two requirements are captured at once by a single order relation
in the star-ordered field `ℂ`: `0 ≤ ⟪T x, x⟫` means `0 ≤ (⟪T x, x⟫).re` together with
`(⟪T x, x⟫).im = 0`. This file records that such a `T` is automatically symmetric (Hermitian),
and, in the finite-dimensional setting N&C works in, self-adjoint (`T† = T`).

## Main results

* `LinearMap.isSymmetric_of_forall_inner_map_self_nonneg`: for `T : E →ₗ[ℂ] E`, if `0 ≤ ⟪T x, x⟫`
  for every `x`, then `T` is symmetric. This is Nielsen & Chuang, Exercise 2.24.
* `LinearMap.isSelfAdjoint_of_forall_inner_map_self_nonneg`: the finite-dimensional consequence,
  `IsSelfAdjoint T` (i.e. `T† = T`), matching N&C's `d`-dimensional operators.
-/

@[expose] public section

open scoped ComplexOrder

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Nielsen & Chuang, Exercise 2.24 (Hermiticity of positive operators).** A positive operator on
a complex inner product space is symmetric (Hermitian). Positivity here is N&C's definition: the
quadratic form `⟪T x, x⟫` is a real, non-negative number for every `x`, encoded by the single
order relation `0 ≤ ⟪T x, x⟫` in the star-ordered field `ℂ`. The hypothesis does not assume
symmetry. -/
theorem isSymmetric_of_forall_inner_map_self_nonneg {T : E →ₗ[ℂ] E}
    (h : ∀ x, 0 ≤ inner ℂ (T x) x) : T.IsSymmetric := sorry

/-- **Nielsen & Chuang, Exercise 2.24**, self-adjoint form. In the finite-dimensional setting N&C
works in, a positive operator `T` on a complex inner product space is self-adjoint, `T† = T`
(`IsSelfAdjoint T`). -/
theorem isSelfAdjoint_of_forall_inner_map_self_nonneg [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}
    (h : ∀ x, 0 ≤ inner ℂ (T x) x) : IsSelfAdjoint T := sorry

end LinearMap
