/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Self-adjointness, norms and sums for `RCLike` fields

## Main results

* `RCLike.isSelfAdjoint_ofReal`: a real coerced into `K` is self-adjoint.
* `RCLike.ofReal_norm_sq_eq_mul_conj`: `((‖z‖ ^ 2 : ℝ) : K) = z * conj z`.
* `RCLike.re_sum`: the real part distributes over finite sums.

-/

@[expose] public section

section
open Fintype
open scoped BigOperators ComplexConjugate
variable {K E : Type*} [RCLike K]
namespace RCLike

theorem isSelfAdjoint_ofReal (r : ℝ) : IsSelfAdjoint ((r : ℝ) : K) := by
  rw [isSelfAdjoint_iff, star_def, conj_ofReal]

end RCLike
end

section
open Fintype
open scoped BigOperators ComplexConjugate
variable {K E : Type*} [RCLike K]
namespace RCLike
variable (K)
variable {K} {z : K}

/-- `push_cast`-friendly reverse of `RCLike.mul_conj`: the real-coerced squared norm
equals `z * conj z`. -/
theorem ofReal_norm_sq_eq_mul_conj (z : K) : ((‖z‖ ^ 2 : ℝ) : K) = z * conj z := by
  rw [mul_conj]; push_cast; ring

end RCLike
end

section
open Fintype
open scoped BigOperators ComplexConjugate
variable {K E : Type*} [RCLike K]
namespace RCLike

/-- The real part distributes over finite sums. -/
theorem re_sum {α : Type*} (s : Finset α) (f : α → K) :
    re (∑ i ∈ s, f i) = ∑ i ∈ s, re (f i) :=
  map_sum (reLm (K := K)) f s

end RCLike
end
