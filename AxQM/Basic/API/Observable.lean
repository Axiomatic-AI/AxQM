/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Observable
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# AxQM.Basic.API — bipartite observables

The tensor product of two observables, and the identity observable.
-/

open scoped InnerProductSpace TensorProduct ComplexOrder

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Tensor product of observables** `A ⊗ B`: the observable of the composite system `S ⊗ T` that
measures `A` on the first factor and `B` on the second. -/
def Observable.tmul (A : Observable S) (B : Observable T) : Observable (S ⊗ T) where
  op := TensorProduct.mapL A.op B.op
  selfAdjoint := IsSelfAdjoint.tensorMapL A.selfAdjoint B.selfAdjoint

@[inherit_doc] scoped infixr:70 " ⊗ " => Observable.tmul

@[simp]
theorem Observable.tmul_op (A : Observable S) (B : Observable T) :
    (A ⊗ B).op = TensorProduct.mapL A.op B.op := rfl

/-- **Action of a tensor observable on a pure tensor:** `(A ⊗ B)(a ⊗ b) = A a ⊗ B b`. -/
theorem Observable.tmul_op_tmul (A : Observable S) (B : Observable T) (a : S.space) (b : T.space) :
    (A ⊗ B).op (a ⊗ₜ[ℂ] b) = A.op a ⊗ₜ[ℂ] B.op b :=
  TensorProduct.mapL_tmul A.op B.op a b

/-- **The tensor of two involutive observables is involutive:** if `A.op² = I` and `B.op² = I` then
`(A ⊗ B).op² = I`. -/
theorem Observable.tmul_op_mul_self {A : Observable S} {B : Observable T}
    (hA : A.op * A.op = 1) (hB : B.op * B.op = 1) :
    (A ⊗ B).op * (A ⊗ B).op = 1 := by
  change TensorProduct.mapL A.op B.op * TensorProduct.mapL A.op B.op = 1
  rw [← TensorProduct.mapL_mul A.op A.op B.op B.op, hA, hB, TensorProduct.mapL_one]

/-- **The identity observable** `I` on a system `S`: the identity operator, self-adjoint. Its
expectation in any state is `1`. -/
def Observable.id (S : QSystem) : Observable S where
  op := 1
  selfAdjoint := IsSelfAdjoint.one _

@[simp] theorem Observable.id_op (S : QSystem) : (Observable.id S).op = 1 := rfl

end AxQM
