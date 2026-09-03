/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # The normalized Gram–Schmidt vectors of a basis span the whole space -/

@[expose] public section

open Finset Submodule

namespace InnerProductSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Applied to a basis `b`, the normalized Gram–Schmidt vectors span the whole space. -/
theorem gramSchmidtNormed_span_eq_top (b : Module.Basis ι 𝕜 E) :
    span 𝕜 (Set.range (gramSchmidtNormed 𝕜 (⇑b))) = ⊤ := sorry

end InnerProductSpace
