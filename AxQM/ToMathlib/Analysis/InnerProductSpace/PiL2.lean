/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reindexing Euclidean space, and extending a linear isometry across spaces

## Main results

* `EuclideanSpace.reindexFinSumEquiv` and `reindexFinProdEquiv`: the isometry equivalences
  reindexing `EuclideanSpace 𝕜 (Fin m ⊕ Fin n)` and `EuclideanSpace 𝕜 (Fin m × Fin n)`.
* `LinearIsometry.extendCross`: a linear isometry from a subspace of `V` into `W` extends to
  all of `V` when `V` and `W` have the same finite dimension.
* `OrthonormalBasis.ne_zero`, `EuclideanSpace.sum_single_ofLp_eq`: supporting facts.

-/

@[expose] public section

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Reindex `EuclideanSpace 𝕜 (Fin m ⊕ Fin n)` to `EuclideanSpace 𝕜 (Fin (m + n))` as a linear
isometric equivalence, via `finSumFinEquiv`. -/
def EuclideanSpace.reindexFinSumEquiv (m n : ℕ) :
    EuclideanSpace 𝕜 (Fin m ⊕ Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (m + n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp]
theorem EuclideanSpace.reindexFinSumEquiv_apply (m n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin m ⊕ Fin n)) :
    (reindexFinSumEquiv m n x : Fin (m + n) → 𝕜) =
      Equiv.piCongrLeft' (fun _ => 𝕜) finSumFinEquiv x :=
  rfl

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

theorem EuclideanSpace.reindexFinSumEquiv_symm (m n : ℕ) :
    (reindexFinSumEquiv (𝕜 := 𝕜) m n).symm =
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm := by
  simp [reindexFinSumEquiv]

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp]
theorem EuclideanSpace.reindexFinSumEquiv_single (m n : ℕ)
    (i : Fin m ⊕ Fin n) (v : 𝕜) :
    reindexFinSumEquiv m n (EuclideanSpace.single i v) =
      EuclideanSpace.single (finSumFinEquiv i) v :=
  EuclideanSpace.piLpCongrLeft_single finSumFinEquiv i v

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Reindex `EuclideanSpace 𝕜 (Fin m × Fin n)` to `EuclideanSpace 𝕜 (Fin (m * n))` as a linear
isometric equivalence, via `finProdFinEquiv`. -/
def EuclideanSpace.reindexFinProdEquiv (m n : ℕ) :
    EuclideanSpace 𝕜 (Fin m × Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (m * n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finProdFinEquiv

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp]
theorem EuclideanSpace.reindexFinProdEquiv_apply (m n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin m × Fin n)) :
    (reindexFinProdEquiv m n x : Fin (m * n) → 𝕜) =
      Equiv.piCongrLeft' (fun _ => 𝕜) finProdFinEquiv x :=
  rfl

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

theorem EuclideanSpace.reindexFinProdEquiv_symm (m n : ℕ) :
    (reindexFinProdEquiv (𝕜 := 𝕜) m n).symm =
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finProdFinEquiv.symm := by
  simp [reindexFinProdEquiv]

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp]
theorem EuclideanSpace.reindexFinProdEquiv_single (m n : ℕ) (i : Fin m × Fin n) (v : 𝕜) :
    reindexFinProdEquiv m n (EuclideanSpace.single i v) =
      EuclideanSpace.single (finProdFinEquiv i) v :=
  EuclideanSpace.piLpCongrLeft_single finProdFinEquiv i v

end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
namespace OrthonormalBasis

lemma ne_zero (b : OrthonormalBasis ι 𝕜 E) (i : ι) : b i ≠ 0 := b.orthonormal.ne_zero i

end OrthonormalBasis
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
namespace EuclideanSpace
variable (𝕜 ι)

/-- A Euclidean-space vector is the sum of its coordinates against the standard basis vectors:
`∑ i, x.ofLp i • single i 1 = x`. -/
theorem sum_single_ofLp_eq {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, x.ofLp i • EuclideanSpace.single i (1 : 𝕜) = x := by
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    OrthonormalBasis.sum_repr (EuclideanSpace.basisFun ι 𝕜) x

end EuclideanSpace
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
open Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}
open Module
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
namespace LinearIsometry

/-- Dimension equality of orthogonal complements when `dim V = dim W` and `L : S →ₗᵢ W` is
an isometric embedding: `dim (range L)ᗮ = dim Sᗮ` (both equal `dim V - dim S`). -/
theorem finrank_orthogonal_range_eq_finrank_orthogonal_of_eq_finrank
    (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) :
    finrank 𝕜 (LinearMap.range L.toLinearMap)ᗮ = finrank 𝕜 Sᗮ :=
  Submodule.finrank_add_finrank_orthogonal' <| by
    rw [LinearMap.finrank_range_of_inj L.injective, S.finrank_add_finrank_orthogonal, hdim]

end LinearIsometry
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
open Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}
open Module
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
namespace LinearIsometry

/-- **Canonical orthogonal-complement isometry** `Sᗮ ≃ₗᵢ (range L)ᗮ`, derived from
`stdOrthonormalBasis` on both subspaces and `finCongr` on the matching dimensions. -/
noncomputable def extendCrossOrthogonalIsometry
    (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) :
    Sᗮ ≃ₗᵢ[𝕜] (LinearMap.range L.toLinearMap)ᗮ :=
  (stdOrthonormalBasis 𝕜 Sᗮ).repr.trans
    ((stdOrthonormalBasis 𝕜 (LinearMap.range L.toLinearMap)ᗮ).reindex <|
      finCongr (finrank_orthogonal_range_eq_finrank_orthogonal_of_eq_finrank hdim L)).repr.symm

end LinearIsometry
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
open Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}
open Module
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
namespace LinearIsometry

-- See the comment on `extendCross_apply` below for the `set_option` rationale.
set_option backward.isDefEq.respectTransparency false in
/-- **Underlying linear map of `LinearIsometry.extendCross`**: extends `L` to `V →ₗ[𝕜] W`
via the canonical decomposition `V = S ⊕ Sᗮ`, mapping `S` by `L` and `Sᗮ` isometrically
onto `(range L)ᗮ` via `extendCrossOrthogonalIsometry`. -/
noncomputable def extendCrossToLinearMap
    (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) : V →ₗ[𝕜] W :=
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  L.toLinearMap.comp S.orthogonalProjection.toLinearMap +
    ((LinearMap.range L.toLinearMap)ᗮ.subtypeₗᵢ.comp
        (extendCrossOrthogonalIsometry hdim L).toLinearIsometry).toLinearMap.comp
      Sᗮ.orthogonalProjection.toLinearMap

end LinearIsometry
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
open Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}
open Module
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
namespace LinearIsometry

set_option backward.isDefEq.respectTransparency false in
/-- Norm-preservation of `extendCrossToLinearMap`. -/
theorem norm_extendCrossToLinearMap_apply (hdim : finrank 𝕜 V = finrank 𝕜 W)
    (L : S →ₗᵢ[𝕜] W) (x : V) :
    ‖extendCrossToLinearMap hdim L x‖ = ‖x‖ := by
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  set p1 : V →ₗ[𝕜] S := S.orthogonalProjection.toLinearMap
  set p2 : V →ₗ[𝕜] Sᗮ := Sᗮ.orthogonalProjection.toLinearMap
  set L3 : Sᗮ →ₗᵢ[𝕜] W := ((LinearMap.range L.toLinearMap)ᗮ).subtypeₗᵢ.comp
    (extendCrossOrthogonalIsometry hdim L).toLinearIsometry
  have Mx_decomp : extendCrossToLinearMap hdim L x = L (p1 x) + L3 (p2 x) := by
    simp [extendCrossToLinearMap, p1, p2, L3]
  have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self L.toLinearMap (p1 x))
      ((extendCrossOrthogonalIsometry hdim L) (p2 x)).property
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S]
  simp only [sq, Mx_decomp]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
  simp only [p1, p2, L3, LinearIsometry.norm_map,
    ContinuousLinearMap.coe_coe, Submodule.coe_norm]

end LinearIsometry
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
open Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}
open Module
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
namespace LinearIsometry

/-- **Cross-space extension**: a linear isometry `L : S →ₗᵢ[𝕜] W` from a subspace of a
finite-dimensional inner product space `V` into a finite-dimensional inner product space
`W` of the same dimension extends to a full isometry `V →ₗᵢ[𝕜] W`. -/
noncomputable def extendCross (hdim : finrank 𝕜 V = finrank 𝕜 W)
    (L : S →ₗᵢ[𝕜] W) : V →ₗᵢ[𝕜] W where
  toLinearMap := extendCrossToLinearMap hdim L
  norm_map' := norm_extendCrossToLinearMap_apply hdim L

end LinearIsometry
end

noncomputable section
open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp
variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable (ι 𝕜)
variable {ι 𝕜}
variable (ι 𝕜 E)
variable [Fintype ι]
variable {ι 𝕜 E}
open Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}
open Module
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
namespace LinearIsometry

-- The `set_option backward.isDefEq.respectTransparency false in` annotation is needed because
-- `FiniteDimensional.complete 𝕜 S` synthesis triggers an `IsUniformAddGroup ↥S` lookup that
-- defeats the default transparency mode on `Submodule` subtypes. Same workaround as on
-- the surrounding `extendCrossToLinearMap` and `norm_extendCrossToLinearMap_apply`.
set_option backward.isDefEq.respectTransparency false in
theorem extendCross_apply (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) (s : S) :
    L.extendCross hdim s = L s := by
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  simp [extendCross, extendCrossToLinearMap]

end LinearIsometry
end
