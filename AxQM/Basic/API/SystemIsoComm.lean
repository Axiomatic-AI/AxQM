/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Associator
import AxQM.Basic.Composite

/-!
# AxQM.Basic.API — the swap system isomorphism

Additions to the **transport backbone** of system isomorphisms (`QSystem.Iso`), siblings of
`QSystem.Iso.refl/symm/trans/tmul` and `QSystem.assoc`:

## Main declarations
* `QSystem.Iso.comm` — the swap iso `S ⊗ T ≃ₛ T ⊗ S`, whose underlying isometry is
  `commIsometry`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The **swap** system isomorphism `S ⊗ T ≃ₛ T ⊗ S`: the two orderings of a bipartite composite are
the same quantum system, with the factors exchanged. The underlying isometry is
`TensorProduct.commIsometry ℂ S.space T.space`. -/
def QSystem.Iso.comm (S T : QSystem) : (S ⊗ T) ≃ₛ (T ⊗ S) :=
  ⟨TensorProduct.commIsometry ℂ S.space T.space⟩

/-- The **left-commutation** system isomorphism `A ⊗ (B ⊗ C) ≃ₛ B ⊗ (A ⊗ C)` — the
transport-backbone counterpart of `TensorProduct.leftComm`. It re-associates to `(A ⊗ B) ⊗ C`,
swaps the front pair to `(B ⊗ A) ⊗ C`, then de-associates to `B ⊗ (A ⊗ C)`, bringing the
*middle* factor `B` to the front while leaving `C` last. A backbone sibling of `QSystem.assoc` /
`QSystem.Iso.comm` / `QSystem.Iso.tmul`. -/
def QSystem.Iso.leftComm (A B C : QSystem) : (A ⊗ (B ⊗ C)) ≃ₛ (B ⊗ (A ⊗ C)) :=
  ((QSystem.assoc A B C).trans ((QSystem.Iso.comm A B).tmul (QSystem.Iso.refl C))).trans
    (QSystem.assoc B A C).symm

end AxQM
