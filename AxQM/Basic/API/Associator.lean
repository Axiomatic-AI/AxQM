/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.SystemIso
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM — the associator system isomorphism `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C`

Composite systems built by the binary tensor `⊗` (`QSystem.compose`) are literally
right-nested or left-nested tensor products of the underlying operators; the physicist regards
`A ⊗ (B ⊗ C)` and `(A ⊗ B) ⊗ C` as the same tripartite system. The **associator**
`QSystem.assoc` is the `QSystem.Iso` witnessing this.

## Main definitions

* `AxQM.QSystem.assoc` — the associator system isomorphism
  `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C`.
* `AxQM.QSystem.Iso.tmul` — the tensor product of two system isomorphisms,
  `(S ⊗ T) ≃ₛ (S' ⊗ T')`; it lets a structural conversion on one factor act inside a composite
  while the other factor is untouched.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable (A B C : QSystem)

/-- The **associator** system isomorphism `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C`: the two nestings
of the tripartite composite are the same quantum system, re-bracketed. -/
def QSystem.assoc : (A ⊗ (B ⊗ C)) ≃ₛ ((A ⊗ B) ⊗ C) :=
  ⟨(TensorProduct.assocIsometry ℂ A.space B.space C.space).symm⟩

/-- The **tensor product of two system isomorphisms** `e : S ≃ₛ S'` and `f : T ≃ₛ T'`, a system
isomorphism `(S ⊗ T) ≃ₛ (S' ⊗ T')`. It lets a structural conversion on one factor (e.g. an
associator) act inside a composite while the other factor is left untouched. -/
def QSystem.Iso.tmul {S S' T T' : QSystem} (e : S ≃ₛ S') (f : T ≃ₛ T') :
    (S ⊗ T) ≃ₛ (S' ⊗ T') :=
  ⟨TensorProduct.congrIsometry e.toIsometry f.toIsometry⟩

end AxQM
