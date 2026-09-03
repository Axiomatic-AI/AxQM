/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The continuous linear map on a tensor product, and its API

## Main results

* `TensorProduct.mapL`: the continuous-linear-map version of `TensorProduct.map` for
  finite-dimensional inner product spaces, with its algebraic API (`_tmul`, `_mul`, `_comp`,
  `_adjoint`, additivity, scalar multiplication, sums).
* `TensorProduct.instCompleteSpace`: a tensor product of finite-dimensional inner product
  spaces is complete.
* `LinearMap.IsSymmetric.tensorMap`, `IsSelfAdjoint.tensorMap`: symmetry and self-adjointness
  are preserved by the tensor product.

-/

@[expose] public section

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module

/-- The tensor product of two finite-dimensional inner product spaces is itself a complete
inner product space. Cannot be derived via `FiniteDimensional.complete` as a global instance
because the latter has an ambiguous `𝕜` parameter; the type `E ⊗[𝕜] F` recovers `𝕜`
unambiguously for this specialization. -/
instance instCompleteSpace [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    CompleteSpace (E ⊗[𝕜] F) := FiniteDimensional.complete 𝕜 _

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module

@[simp] lemma congrIsometry_tmul (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (a : E) (b : F) :
    congrIsometry f g (a ⊗ₜ[𝕜] b) = f a ⊗ₜ[𝕜] g b := rfl

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The tensor product of two symmetric linear maps is symmetric. -/
theorem _root_.LinearMap.IsSymmetric.tensorMap [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric) :
    (TensorProduct.map A B).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint] at hA hB ⊢
  rw [LinearMap.isSelfAdjoint_iff'] at hA hB ⊢
  rw [TensorProduct.adjoint_map, hA, hB]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The tensor product of two self-adjoint linear maps is self-adjoint. -/
theorem _root_.IsSelfAdjoint.tensorMap [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] E} (hA : IsSelfAdjoint A) {B : F →ₗ[𝕜] F} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (TensorProduct.map A B) := by
  rw [LinearMap.isSelfAdjoint_iff'] at hA hB ⊢
  rw [TensorProduct.adjoint_map, hA, hB]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- **Continuous linear map version of `TensorProduct.map`** (finite-dim case): for continuous
linear maps `f : E →L[𝕜] F` and `g : G →L[𝕜] H` between finite-dim inner product spaces, the
tensor product map `E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H`. -/
noncomputable def mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H :=
  (TensorProduct.map f.toLinearMap g.toLinearMap).toContinuousLinearMap

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

@[simp]
theorem mapL_toLinearMap [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapL f g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap :=
  rfl

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

@[simp]
theorem mapL_apply [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) (x : E ⊗[𝕜] G) :
    mapL f g x = TensorProduct.map f.toLinearMap g.toLinearMap x := rfl

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

@[simp]
theorem mapL_tmul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) (a : E) (b : G) :
    mapL f g (a ⊗ₜ[𝕜] b) = f a ⊗ₜ[𝕜] g b :=
  rfl

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The tensor-product map distributes over composition: `mapL (f₁ * f₂) (g₁ * g₂)
= mapL f₁ g₁ * mapL f₂ g₂`. -/
@[simp]
theorem mapL_mul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f₁ f₂ : E →L[𝕜] E) (g₁ g₂ : F →L[𝕜] F) :
    mapL (f₁ * f₂) (g₁ * g₂) = mapL f₁ g₁ * mapL f₂ g₂ := by
  ext x
  simp [TensorProduct.map_mul]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The tensor-product map distributes over composition: `mapL f₂ g₂ ∘L mapL f₁ g₁
= mapL (f₂ ∘L f₁) (g₂ ∘L g₁)`. -/
theorem mapL_comp {F' H' : Type*} [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F']
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] [FiniteDimensional 𝕜 H']
    (f₂ : F →L[𝕜] F') (g₂ : H →L[𝕜] H') (f₁ : E →L[𝕜] F) (g₁ : G →L[𝕜] H) :
    (mapL f₂ g₂).comp (mapL f₁ g₁) = mapL (f₂.comp f₁) (g₂.comp g₁) := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.coe_comp, mapL_toLinearMap, mapL_toLinearMap, mapL_toLinearMap,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp, TensorProduct.map_comp]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` of identity operators is the identity. -/
@[simp]
theorem mapL_one [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    mapL (1 : E →L[𝕜] E) (1 : F →L[𝕜] F) = 1 := by
  ext x
  simp [TensorProduct.map_one]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL · 1` is multiplicative: `mapL (f₁ * f₂) 1 = mapL f₁ 1 * mapL f₂ 1`, i.e. the left
embedding `f ↦ f ⊗ 1` is a monoid homomorphism. -/
theorem mapL_mul_one [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f₁ f₂ : E →L[𝕜] E) :
    mapL (f₁ * f₂) (1 : F →L[𝕜] F) = mapL f₁ 1 * mapL f₂ 1 := by
  simpa using mapL_mul f₁ f₂ (1 : F →L[𝕜] F) 1

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The adjoint of a tensor-product map is the tensor product of the adjoints:
`(mapL f g)† = mapL f† g†`. -/
@[simp]
theorem mapL_adjoint [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]
    (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapL f g).adjoint = mapL f.adjoint g.adjoint := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.adjoint_toLinearMap, mapL_toLinearMap, mapL_toLinearMap,
    TensorProduct.adjoint_map, ContinuousLinearMap.adjoint_toLinearMap,
    ContinuousLinearMap.adjoint_toLinearMap]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The tensor product of two unitary operators is unitary: if `f` and `g` are unitary,
so is `mapL f g`. -/
theorem mapL_mem_unitary [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    {f : E →L[𝕜] E} {g : F →L[𝕜] F}
    (hf : f ∈ unitary (E →L[𝕜] E)) (hg : g ∈ unitary (F →L[𝕜] F)) :
    mapL f g ∈ unitary (E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F) := by
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hf hg ⊢
  rw [mapL_adjoint]
  refine ⟨?_, ?_⟩
  · rw [← mapL_mul, hf.1, hg.1, mapL_one]
  · rw [← mapL_mul, hf.2, hg.2, mapL_one]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- The conjugate-square of a tensor-product map factors over the slots:
`(mapL f g)† ∘ mapL f g = mapL (f† ∘ f) (g† ∘ g)`. -/
theorem mapL_adjoint_comp_self [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] [CompleteSpace H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapL f g).adjoint ∘L mapL f g = mapL (f.adjoint ∘L f) (g.adjoint ∘L g) := by
  rw [mapL_adjoint, mapL_comp]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` is additive in the first argument: `mapL (f₁ + f₂) g = mapL f₁ g + mapL f₂ g`. -/
theorem mapL_add_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (f₁ + f₂) g = mapL f₁ g + mapL f₂ g := by
  ext x; simp [TensorProduct.map_add_left]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` is zero when the first argument is zero: `mapL 0 g = 0`. -/
theorem mapL_zero_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (g : G →L[𝕜] H) :
    mapL (0 : E →L[𝕜] F) g = 0 := by
  ext x; simp [TensorProduct.map_zero_left]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` is additive in the second argument: `mapL f (g₁ + g₂) = mapL f g₁ + mapL f g₂`. -/
theorem mapL_add_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    mapL f (g₁ + g₂) = mapL f g₁ + mapL f g₂ := by
  ext x; simp [TensorProduct.map_add_right]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` is `𝕜`-homogeneous in the first argument: `mapL (c • f) g = c • mapL f g`. -/
theorem mapL_smul_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (c : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (c • f) g = c • mapL f g := by
  ext x; simp [TensorProduct.map_smul_left]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` is `𝕜`-homogeneous in the second argument: `mapL f (c • g) = c • mapL f g`. -/
theorem mapL_smul_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (c : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f (c • g) = c • mapL f g := by
  ext x; simp [TensorProduct.map_smul_right]

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` factors via two "tensor-by-identity" maps composed: `mapL f g = mapL f 1 ∘ mapL 1 g`. -/
theorem mapL_factor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f g = (mapL f (1 : H →L[𝕜] H)).comp (mapL (1 : E →L[𝕜] E) g) := by
  refine ContinuousLinearMap.coe_injective (TensorProduct.ext' fun a b ↦ ?_)
  simp

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL · 1` as a `LinearMap`: linear in the first argument. -/
private noncomputable def mapL_one_right_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 H] :
    (E →L[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] H →L[𝕜] F ⊗[𝕜] H) where
  toFun f := mapL f (1 : H →L[𝕜] H)
  map_add' f₁ f₂ := mapL_add_left f₁ f₂ 1
  map_smul' c f := mapL_smul_left c f 1

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL 1 ·` as a `LinearMap`: linear in the second argument. -/
private noncomputable def mapL_one_left_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] :
    (G →L[𝕜] H) →ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] H) where
  toFun g := mapL (1 : E →L[𝕜] E) g
  map_add' g₁ g₂ := mapL_add_right 1 g₁ g₂
  map_smul' c g := mapL_smul_right c 1 g

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL 1 ·` distributes over finite sums in the second argument:
`mapL 1 (∑ k, g k) = ∑ k, mapL 1 (g k)`. -/
theorem mapL_one_sum_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]
    {n : Type*} [Fintype n] (g : n → (G →L[𝕜] H)) :
    mapL (1 : E →L[𝕜] E) (∑ k, g k) = ∑ k, mapL (1 : E →L[𝕜] E) (g k) :=
  map_sum (mapL_one_left_LM (E := E)) g Finset.univ

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL · g` as a `LinearMap`: linear in the first argument. -/
private noncomputable def mapL_rightArg_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] (g : G →L[𝕜] H) :
    (E →L[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) where
  toFun f := mapL f g
  map_add' f₁ f₂ := mapL_add_left f₁ f₂ g
  map_smul' c f := mapL_smul_left c f g

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL f ·` as a `LinearMap`: linear in the second argument. -/
private noncomputable def mapL_leftArg_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) :
    (G →L[𝕜] H) →ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) where
  toFun g := mapL f g
  map_add' g₁ g₂ := mapL_add_right f g₁ g₂
  map_smul' c g := mapL_smul_right c f g

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` distributes over finite sums in the first argument:
`mapL (∑ k, A k) g = ∑ k, mapL (A k) g`. -/
theorem mapL_sum_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] {n : Type*} [Fintype n] (A : n → (E →L[𝕜] F)) (g : G →L[𝕜] H) :
    mapL (∑ k, A k) g = ∑ k, mapL (A k) g :=
  map_sum (mapL_rightArg_LM g) A Finset.univ

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- `mapL` distributes over finite sums in the second argument:
`mapL f (∑ k, B k) = ∑ k, mapL f (B k)`. -/
theorem mapL_sum_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] {n : Type*} [Fintype n] (f : E →L[𝕜] F) (B : n → (G →L[𝕜] H)) :
    mapL f (∑ k, B k) = ∑ k, mapL f (B k) :=
  map_sum (mapL_leftArg_LM f) B Finset.univ

end TensorProduct
end

section
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
open scoped TensorProduct
namespace TensorProduct
open scoped ComplexOrder
open Module
open LinearMap

/-- **Joint continuity of `mapL`**: for continuous `f : β → E →L[𝕜] F` and `g : β → G →L[𝕜] H`
(`β` topological, all spaces finite-dim), `b ↦ mapL (f b) (g b)` is continuous. -/
theorem _root_.Continuous.mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]
    {β : Type*} [TopologicalSpace β]
    {f : β → E →L[𝕜] F} {g : β → G →L[𝕜] H}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun b ↦ TensorProduct.mapL (f b) (g b)) :=
  (isBoundedBilinearMap_comp.continuous.comp (Continuous.prodMk
    ((TensorProduct.mapL_one_right_LM (E := E) (F := F) (H := H)
      (𝕜 := 𝕜)).continuous_of_finiteDimensional.comp hf)
    ((TensorProduct.mapL_one_left_LM (E := E) (G := G) (H := H)
      (𝕜 := 𝕜)).continuous_of_finiteDimensional.comp hg))).congr
    fun b ↦ (TensorProduct.mapL_factor (f b) (g b)).symm

end TensorProduct
end
