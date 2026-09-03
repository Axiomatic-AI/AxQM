/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-! # The partial isometry identifying two orthonormal families

Given two orthonormal families `a : ι → E` and `b : ι → F` of the same finite size (in possibly
*different* inner product spaces `E`, `F`), this file introduces the **cross-synthesis operator**
`∑ i, |a i⟩⟨b i| : F →L[𝕜] E`, the partial isometry sending `b i` to `a i`.
-/

@[expose] public section

open scoped InnerProductSpace
open Finset

namespace InnerProductSpace

/-- The **cross-synthesis operator** `∑ i, |a i⟩⟨b i| : F →L[𝕜] E` of two finite families `a : ι →
E`, `b : ι → F`. When `a`, `b` are orthonormal of the same size it is the partial isometry
identifying the family `b` with the family `a` (`b i ↦ a i`), i.e. the operator whose "matrix"
in the bases `b`, `a` is the identity. -/
noncomputable def crossSynthesis (𝕜 : Type*) {E F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι]
    (a : ι → E) (b : ι → F) : F →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (a i) (b i)

end InnerProductSpace
