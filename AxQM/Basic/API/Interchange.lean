/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SystemIsoComm
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProductInterchange
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# AxQM.Basic.API — four-factor interchange system isomorphisms

Structural reshapes of a fourfold composite: `(A ⊗ B) ⊗ (C ⊗ D)` is the same quantum system
however its four factors are re-bracketed and re-ordered.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable (A B C D : QSystem)

/-- The **interchange braid** system isomorphism `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (A ⊗ C) ⊗ (B ⊗ D)`:
the two inner factors `B` and `C` of a fourfold composite are exchanged, a pure regrouping of the
same four systems. -/
def QSystem.Iso.interchange : ((A ⊗ B) ⊗ (C ⊗ D)) ≃ₛ ((A ⊗ C) ⊗ (B ⊗ D)) :=
  ⟨TensorProduct.tensorTensorTensorCommIsometry ℂ A.space B.space C.space D.space⟩

/-- The **BCAD interchange** system isomorphism `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (B ⊗ C) ⊗ (A ⊗ D)`: the
four-factor permutation `(A, B, C, D) ↦ (B, C, A, D)`, exposing `B ⊗ C` as the left factor and
`A ⊗ D` as the right factor of a fourfold composite. -/
def QSystem.interchangeBCAD : ((A ⊗ B) ⊗ (C ⊗ D)) ≃ₛ ((B ⊗ C) ⊗ (A ⊗ D)) :=
  (QSystem.Iso.tmul (QSystem.Iso.comm A B) (QSystem.Iso.refl (C ⊗ D))).trans
    (QSystem.Iso.interchange B A C D)

end AxQM
