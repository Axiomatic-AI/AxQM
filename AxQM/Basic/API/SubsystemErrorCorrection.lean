/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumErrorCorrection
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — correcting arbitrary errors on a subsystem

Infrastructure for **Nielsen & Chuang, Exercise 12.14** (p. 567): the reference system `R` and the
subsystem `Q₁` on which errors are to be corrected must be *uncorrelated*, `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1}`,
and this decoupling is *sufficient* for the errors on `Q₁` to be correctable.

## Contents

* `AxQM.leftFactorOp` — the lift `A ↦ A ⊗ I_{Q₂}` of a `Q₁`-operator to `Q₁ ⊗ Q₂`.
* `AxQM.leftFactorErrorBasis` — the complete matrix-unit error family `{|b a⟩⟨b c| ⊗ I}`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

variable {Q₁ Q₂ : QSystem}

/-- The lift `A ↦ A ⊗ I_{Q₂}` of an operator on the left factor `Q₁` to the composite `Q₁ ⊗ Q₂`
(the operator that acts by `A` on `Q₁` and does nothing on `Q₂`). -/
def leftFactorOp (A : Q₁.space →L[ℂ] Q₁.space) : (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space :=
  TensorProduct.mapL A (1 : Q₂.space →L[ℂ] Q₂.space)

/-- The **complete family of errors on the left factor `Q₁`**, in an orthonormal basis `b` of
`Q₁.space`: the matrix units `|b a⟩⟨b c|` acting on `Q₁`, tensored with the identity on `Q₂`,
`leftFactorErrorBasis b (a, c) = |b a⟩⟨b c| ⊗ I_{Q₂}` (indexed by `ι × ι`). -/
def leftFactorErrorBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ Q₁.space) :
    ι × ι → ((Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space) :=
  fun p => leftFactorOp (rankOne ℂ (b p.1) (b p.2))

end AxQM
