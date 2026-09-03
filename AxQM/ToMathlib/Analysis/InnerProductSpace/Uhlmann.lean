/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PolarUnitary
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# Uhlmann's theorem, operator form

Operator facts about the continuous-functional-calculus square root `√a` of an operator on a
finite-dimensional complex inner product space.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

namespace ContinuousLinearMap

omit [FiniteDimensional ℂ E] in
/-- The **CFC real square root of an operator is self-adjoint**, `(√a)† = √a`. -/
theorem adjoint_cfc_real_sqrt (a : E →L[ℂ] E) :
    adjoint (cfc Real.sqrt a) = cfc Real.sqrt a := by
  rw [← star_eq_adjoint]; exact IsSelfAdjoint.cfc

end ContinuousLinearMap
