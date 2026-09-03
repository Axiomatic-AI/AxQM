/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The trace of an adjoint composition, and trace under conjugation

## Main results

* `LinearMap.re_trace_adjoint_comp_self_eq_sum_norm_sq` and the vanishing criterion that
  follows from it.
* `ContinuousLinearMap.trace_conjStarAlgEquiv`, `trace_conj_isometry`: the trace is invariant
  under conjugation by an isometry.

-/

@[expose] public section

section
namespace LinearMap
variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
open scoped InnerProductSpace ComplexOrder
variable [FiniteDimensional 𝕜 E]
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The trace of `T† ∘ T` has a basis-sum form: `re trace (T† ∘ T) = ∑ i, ‖T (b i)‖²`
for any orthonormal basis. -/
theorem re_trace_adjoint_comp_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    (T : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    RCLike.re ((T.adjoint ∘ₗ T).trace 𝕜 E) = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [trace_eq_sum_inner _ b, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

end LinearMap
end

section
namespace LinearMap
variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
open scoped InnerProductSpace ComplexOrder
variable [FiniteDimensional 𝕜 E]
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **Non-degeneracy of the HS pairing**: a linear map `T : E →ₗ[𝕜] F` between
finite-dim inner product spaces with `trace (T† ∘ T) = 0` must be zero. -/
theorem eq_zero_of_trace_adjoint_comp_self_eq_zero (T : E →ₗ[𝕜] F)
    (h : (T.adjoint ∘ₗ T).trace 𝕜 E = 0) : T = 0 := by
  set b := stdOrthonormalBasis 𝕜 E
  refine b.toBasis.ext fun i ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.zero_apply, ← norm_eq_zero, ← sq_eq_zero_iff]
  have h_sum := T.re_trace_adjoint_comp_self_eq_sum_norm_sq b
  rw [h, map_zero] at h_sum
  exact (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp h_sum.symm i
    (Finset.mem_univ _)

end LinearMap
end

section
namespace LinearMap
variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
open scoped InnerProductSpace ComplexOrder
variable [FiniteDimensional 𝕜 E]
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- *Spectral expansion of `trace (M ∘ T)`*: for a symmetric operator `T` with eigenvalues
`λⱼ` and eigenvector ONB `bⱼ`, and any linear operator `M`, the trace of `M ∘ T` factors as
`∑ j, λⱼ * ⟪bⱼ, M bⱼ⟫`. Foundational for finite-dim quantum information theory (Born rule,
expectation values, density-matrix traces). -/
theorem IsSymmetric.trace_comp_eq_sum_eigenvalues_inner
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (M : E →ₗ[𝕜] E) :
    LinearMap.trace 𝕜 E (M ∘ₗ T) =
      ∑ j, (hT.eigenvalues hn j : 𝕜) *
        inner 𝕜 (hT.eigenvectorBasis hn j) (M (hT.eigenvectorBasis hn j)) := by
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, hT.apply_eigenvectorBasis hn j,
    LinearMap.map_smul, inner_smul_right]

end LinearMap
end

section
namespace ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- **Trace invariance under conjugation by a linear isometry equivalence.** The trace of
`T : E →L[𝕜] E` and `e.conjStarAlgEquiv T : F →L[𝕜] F` agree. -/
@[simp]
theorem trace_conjStarAlgEquiv [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    LinearMap.trace 𝕜 F ((e.conjStarAlgEquiv T : F →L[𝕜] F) : F →ₗ[𝕜] F) =
      LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap]
  exact LinearMap.trace_conj' _ _

end ContinuousLinearMap
end

section
namespace ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Trace invariance under conjugation by a (possibly non-surjective) isometry.** For
`V : E →L[𝕜] F` with `V† V = 1`, `tr_F (V A V†) = tr_E A`. -/
theorem trace_conj_isometry [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F]
    {V : E →L[𝕜] F} (hV : V.adjoint ∘L V = 1) (A : E →L[𝕜] E) :
    LinearMap.trace 𝕜 F (V ∘L A ∘L V.adjoint : F →L[𝕜] F).toLinearMap
      = LinearMap.trace 𝕜 E A.toLinearMap := by
  rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
    ← LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← ContinuousLinearMap.coe_comp, hV]
  congr 1

end ContinuousLinearMap
end
