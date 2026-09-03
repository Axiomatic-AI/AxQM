/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# The trace without a finite basis

## Main results

* `LinearMap.trace_eq_zero_of_not_exists_finset_basis` and its apply-form: the trace is `0`
  when the module admits no finite basis.

-/

@[expose] public section

namespace LinearMap

section
universe u v w
open scoped Matrix
open Module TensorProduct
variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [DecidableEq ι] [Fintype ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ]
variable (b : Basis ι R M) (c : Basis κ R M)

/-- The trace of an endomorphism vanishes when there is no finite basis. -/
theorem trace_eq_zero_of_not_exists_finset_basis
    (h : ¬ ∃ s : Finset M, Nonempty (Basis s R M)) :
    trace R M = 0 := by
  rw [trace, dif_neg h]

end

section
universe u v w
open scoped Matrix
open Module TensorProduct
variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [DecidableEq ι] [Fintype ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ]
variable (b : Basis ι R M) (c : Basis κ R M)

/-- Apply-form of `trace_eq_zero_of_not_exists_finset_basis`. -/
theorem trace_apply_eq_zero_of_not_exists_finset_basis
    (h : ¬ ∃ s : Finset M, Nonempty (Basis s R M)) (f : M →ₗ[R] M) :
    trace R M f = 0 := by
  rw [trace_eq_zero_of_not_exists_finset_basis R h, LinearMap.zero_apply]

end

end LinearMap
