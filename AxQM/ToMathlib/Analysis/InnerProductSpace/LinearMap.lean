/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import AxQM.ToMathlib.Analysis.RCLike.Basic

/-!
# Rank-one operators and the real quadratic form

## Main results

* `InnerProductSpace.rankOne_smul_smul`, `rankOne_smul_smul_self`,
  `rankOne_real_sqrt_smul_self`, `rankOne_sum_smul_sum_smul`: scalar and sum identities for
  rank-one operators.
* `ContinuousLinearMap.reApplyInnerSelf_ofReal_smul`, `reApplyInnerSelf_sum`,
  `reApplyInnerSelf_rankOne_self`: the corresponding identities for `reApplyInnerSelf`.

-/

@[expose] public section

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem ContinuousLinearMap.reApplyInnerSelf_ofReal_smul (T : E →L[𝕜] E) (x : E) (r : ℝ) :
    ((r : 𝕜) • T).reApplyInnerSelf x = r * T.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, conj_ofReal, re_ofReal_mul]

end

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem ContinuousLinearMap.reApplyInnerSelf_sum {ι : Type*} (s : Finset ι)
    (T : ι → E →L[𝕜] E) (x : E) :
    (∑ i ∈ s, T i).reApplyInnerSelf x = ∑ i ∈ s, (T i).reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sum_apply,
    sum_inner, re_sum]

end

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]
open ContinuousLinearMap

/-- Sesquilinearity of `rankOne` in both arguments: scalars on the left factor through linearly,
scalars on the right factor through conjugate-linearly. -/
lemma rankOne_smul_smul (s t : 𝕜) (x : E) (y : F) :
    rankOne 𝕜 (s • x) (t • y) = (s * starRingEnd 𝕜 t) • rankOne 𝕜 x y := by
  ext z
  simp [rankOne_apply, smul_smul, mul_assoc, mul_left_comm]

end InnerProductSpace
end

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]
open ContinuousLinearMap

/-- Same scalar in both arguments:
`rankOne 𝕜 (s • x) (s • x) = (s * star s) • rankOne 𝕜 x x`. -/
lemma rankOne_smul_smul_self (s : 𝕜) (x : F) :
    rankOne 𝕜 (s • x) (s • x) = (s * starRingEnd 𝕜 s) • rankOne 𝕜 x x :=
  rankOne_smul_smul s s x x

end InnerProductSpace
end

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]
open ContinuousLinearMap

/-- Absorbing a real square root scalar into a rank-one self-projector picks up the squared
scalar. -/
lemma rankOne_real_sqrt_smul_self {r : ℝ} (hr : 0 ≤ r) (x : F) :
    rankOne 𝕜 ((Real.sqrt r : 𝕜) • x) ((Real.sqrt r : 𝕜) • x)
      = (r : 𝕜) • rankOne 𝕜 x x := by
  rw [rankOne_smul_smul_self, RCLike.conj_ofReal, ← RCLike.ofReal_mul, Real.mul_self_sqrt hr]

end InnerProductSpace
end

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]
open ContinuousLinearMap

/-- **Bilinearity of `rankOne` over finite sums of smul-combinations**: distributing both
arguments of `rankOne` as linear combinations produces a double sum, with the antilinearity
in the second argument appearing as `star (d j)` on the scalar:
`rankOne 𝕜 (∑ i, c i • a i) (∑ j, d j • b j)`
  `= ∑ i, ∑ j, (c i * star (d j)) • rankOne 𝕜 (a i) (b j)`. -/
lemma rankOne_sum_smul_sum_smul {ι ι' : Type*} (s : Finset ι) (s' : Finset ι')
    (a : ι → E) (b : ι' → F) (c : ι → 𝕜) (d : ι' → 𝕜) :
    rankOne 𝕜 (∑ i ∈ s, c i • a i) (∑ j ∈ s', d j • b j) =
      ∑ i ∈ s, ∑ j ∈ s', (c i * starRingEnd 𝕜 (d j)) • rankOne 𝕜 (a i) (b j) := by
  ext z
  simp only [rankOne_apply, sum_inner, inner_smul_left,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    Finset.smul_sum, Finset.sum_mul, Finset.sum_smul, smul_smul]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring_nf

end InnerProductSpace
end

section
open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
namespace ContinuousLinearMap
open InnerProductSpace
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The `reApplyInnerSelf` of a rank-one self projector `|d⟩⟨d|`: the real part of
`⟪|d⟩⟨d| x, x⟫` is `‖⟪d, x⟫‖²`. -/
theorem reApplyInnerSelf_rankOne_self (d x : E) :
    (rankOne 𝕜 d d).reApplyInnerSelf x = ‖inner 𝕜 d x‖ ^ 2 := by
  rw [reApplyInnerSelf_apply, rankOne_apply, inner_smul_left, RCLike.conj_mul]
  simp

end ContinuousLinearMap
end
