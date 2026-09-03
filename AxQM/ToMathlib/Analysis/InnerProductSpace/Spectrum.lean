/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import AxQM.ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral sums and eigenvalues of symmetric and idempotent operators

## Main results

* `LinearMap.IsSymmetric.spectral_sum_apply`, `IsSelfAdjoint.spectral_sum`: a self-adjoint
  operator as the sum of its eigenvalues weighted by rank-one projectors.
* `IsIdempotentElem.eigenvalues_zero_or_one`: an idempotent has eigenvalues `0` or `1`.

-/

@[expose] public section

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
namespace LinearMap
namespace IsSymmetric
variable {T : E →ₗ[𝕜] E}
variable [FiniteDimensional 𝕜 E]
variable {n : ℕ}

/-- For a symmetric `T`, the Gram operator `T† ∘ T` acts on `T`'s eigenbasis by scaling each
basis vector by the square of the corresponding eigenvalue. -/
theorem adjoint_comp_self_apply_eigenvectorBasis (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    (T.adjoint ∘ₗ T) (hT.eigenvectorBasis hn i) =
      ((hT.eigenvalues hn i) ^ 2 : 𝕜) • hT.eigenvectorBasis hn i := by
  rw [LinearMap.comp_apply, hT.adjoint_eq, hT.apply_eigenvectorBasis,
    LinearMap.map_smul, hT.apply_eigenvectorBasis, smul_smul]
  ring_nf

end IsSymmetric
end LinearMap
end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
namespace LinearMap
namespace IsSymmetric
variable {T : E →ₗ[𝕜] E}
variable [FiniteDimensional 𝕜 E]
variable {n : ℕ}

/-- *Spectral expansion, vector form*: applying a self-adjoint operator on a finite-dimensional
inner product space to a vector yields the sum of the eigenvalues weighted by the inner-product
coefficients along the eigenvectors. -/
theorem spectral_sum_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) :
    T v = ∑ i, (hT.eigenvalues hn i : 𝕜) • ⟪hT.eigenvectorBasis hn i, v⟫ •
      hT.eigenvectorBasis hn i := by
  conv_lhs => rw [← (hT.eigenvectorBasis hn).sum_repr' v]
  simp_rw [map_sum, map_smul, hT.apply_eigenvectorBasis hn, smul_smul, mul_comm]

end IsSymmetric
end LinearMap
end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
namespace LinearMap
namespace IsSymmetric
variable {T : E →ₗ[𝕜] E}
variable [FiniteDimensional 𝕜 E]
variable {n : ℕ}

open Polynomial in
/-- **Eigenvalue recognition theorem**: if a symmetric operator `T` admits an eigenbasis with
real eigenvalues `μ`, then the multiset of those eigenvalues equals the multiset of `T`'s
canonical eigenvalues. The eigenbasis can be indexed by any `Fintype`. -/
theorem eigenvalues_multiset_map_eq_of_eigenbasis (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 E) {μ : ι → ℝ}
    (heigen : ∀ i, T (b i) = (μ i : 𝕜) • b i) :
    Multiset.map μ Finset.univ.val = Multiset.map (hT.eigenvalues hn) Finset.univ.val := by
  classical
  have hmat : LinearMap.toMatrix b b T = Matrix.diagonal (fun i => (μ i : 𝕜)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, heigen, Matrix.diagonal_apply, Basis.repr_self,
      Finsupp.single_apply, eq_comm, RCLike.real_smul_eq_coe_mul]
    grind
  have hcharpoly : T.charpoly = ∏ i, (X - C ((μ i : 𝕜))) := by
    rw [← T.charpoly_toMatrix b, hmat, Matrix.charpoly_diagonal]
  have hroots : T.charpoly.roots =
      Multiset.map ((RCLike.ofReal : ℝ → 𝕜) ∘ μ) Finset.univ.val := by
    rw [hcharpoly,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])]
    simp
  have hcast := hroots.symm.trans (hT.roots_charpoly_eq_eigenvalues hn)
  rw [← Multiset.map_map, ← Multiset.map_map] at hcast
  exact Multiset.map_injective RCLike.ofReal_injective hcast

end IsSymmetric
end LinearMap
end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp

/-- If two functions `Fin n → α` (with `α` a linear order) have equal multisets of values and are
both antitone (sorted nonincreasingly via `List.ofFn`), they agree pointwise. -/
theorem antitone_eq_of_multiset_map_eq {n : ℕ} {α : Type*} [LinearOrder α]
    {f g : Fin n → α} (hf : Antitone f) (hg : Antitone g)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    f = g := by
  have hperm : (List.ofFn f).Perm (List.ofFn g) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
    exact h
  exact List.ofFn_inj.mp
    (List.Perm.eq_of_sortedGE hf.sortedGE_ofFn hg.sortedGE_ofFn hperm)

end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The eigenvalues of a symmetric idempotent linear map (an orthogonal projection)
square to themselves: `λᵢ² = λᵢ`. -/
theorem IsIdempotentElem.eigenvalues_sq_eq_self {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hidem : IsIdempotentElem T) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.eigenvalues hn i ^ 2 = hT.eigenvalues hn i := by
  set b := hT.eigenvectorBasis hn
  have hTb : T (b i) = (hT.eigenvalues hn i : 𝕜) • b i := hT.apply_eigenvectorBasis hn i
  have h_lhs : T (T (b i)) = (hT.eigenvalues hn i : 𝕜) ^ 2 • b i := by
    rw [hTb, map_smul, hTb, smul_smul, sq]
  have hidem' : T (T (b i)) = T (b i) := congr_arg (· (b i)) hidem
  rw [h_lhs, hTb] at hidem'
  have h_scalar : ((hT.eigenvalues hn i : 𝕜) ^ 2 : 𝕜) = (hT.eigenvalues hn i : 𝕜) :=
    smul_left_injective 𝕜 (b.ne_zero i) hidem'
  exact_mod_cast h_scalar

end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Each eigenvalue of a symmetric idempotent linear map (an orthogonal projection) is
either `0` or `1`. -/
theorem IsIdempotentElem.eigenvalues_zero_or_one {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hidem : IsIdempotentElem T) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.eigenvalues hn i = 0 ∨ hT.eigenvalues hn i = 1 := by
  have h := hidem.eigenvalues_sq_eq_self hT hn i
  have hfact : hT.eigenvalues hn i * (hT.eigenvalues hn i - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hfact with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
namespace IsSelfAdjoint
variable [CompleteSpace E] [FiniteDimensional 𝕜 E] {T : E →L[𝕜] E} {n : ℕ}

/-- *Spectral expansion, vector form*: applying a self-adjoint continuous linear map on a
finite-dimensional inner product space to a vector yields the sum of the eigenvalues weighted by
the inner-product coefficients along the eigenvectors. -/
theorem spectral_sum_apply (hT : IsSelfAdjoint T) (hn : Module.finrank 𝕜 E = n) (v : E) :
    T v = ∑ i, (hT.isSymmetric.eigenvalues hn i : 𝕜) •
      ⟪hT.isSymmetric.eigenvectorBasis hn i, v⟫ • hT.isSymmetric.eigenvectorBasis hn i :=
  hT.isSymmetric.spectral_sum_apply hn v

end IsSelfAdjoint
end

section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open scoped ComplexConjugate
open Module End WithLp
namespace IsSelfAdjoint
variable [CompleteSpace E] [FiniteDimensional 𝕜 E] {T : E →L[𝕜] E} {n : ℕ}

/-- *Spectral expansion, operator form*: a self-adjoint continuous linear map on a
finite-dimensional inner product space equals the sum of its eigenvalues weighted by the rank-one
operators along the (orthonormal) eigenvectors. -/
theorem spectral_sum (hT : IsSelfAdjoint T) (hn : Module.finrank 𝕜 E = n) :
    T = ∑ i, (hT.isSymmetric.eigenvalues hn i : 𝕜) •
      InnerProductSpace.rankOne 𝕜 (hT.isSymmetric.eigenvectorBasis hn i)
        (hT.isSymmetric.eigenvectorBasis hn i) := by
  ext v
  rw [hT.spectral_sum_apply hn v]
  simp [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply]

end IsSelfAdjoint
end
