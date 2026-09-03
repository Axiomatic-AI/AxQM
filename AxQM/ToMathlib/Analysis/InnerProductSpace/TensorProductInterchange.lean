/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The middle-two interchange isometry on a fourfold tensor product

For inner product spaces `E, F, G, H`, the rearrangement
`(E ⊗ F) ⊗ (G ⊗ H) ≃ₗᵢ[𝕜] (E ⊗ G) ⊗ (F ⊗ H)` that swaps the two middle factors, packaged as an
isometry so it transports the inner-product / norm structure.

## Main definitions

* `TensorProduct.tensorTensorTensorCommIsometry` — the interchange isometry equivalence.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E F G H : Type*)
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **middle-two interchange isometry**: the inner-product-preserving rearrangement
`(E ⊗ F) ⊗ (G ⊗ H) ≃ₗᵢ (E ⊗ G) ⊗ (F ⊗ H)` swapping the two middle factors `F` and `G`. -/
noncomputable def tensorTensorTensorCommIsometry :
    (E ⊗[𝕜] F) ⊗[𝕜] (G ⊗[𝕜] H) ≃ₗᵢ[𝕜] (E ⊗[𝕜] G) ⊗[𝕜] (F ⊗[𝕜] H) :=
  (assocIsometry 𝕜 E F (G ⊗[𝕜] H)).trans
    ((congrIsometry (LinearIsometryEquiv.refl 𝕜 E) (assocIsometry 𝕜 F G H).symm).trans
      ((congrIsometry (LinearIsometryEquiv.refl 𝕜 E)
          (congrIsometry (commIsometry 𝕜 F G) (LinearIsometryEquiv.refl 𝕜 H))).trans
        ((congrIsometry (LinearIsometryEquiv.refl 𝕜 E) (assocIsometry 𝕜 G F H)).trans
          (assocIsometry 𝕜 E G (F ⊗[𝕜] H)).symm)))

end TensorProduct
