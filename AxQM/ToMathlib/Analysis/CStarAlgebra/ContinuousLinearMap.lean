/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Continuous functional calculus on the operators of a complex Hilbert space

## Main results

* `ContinuousLinearMap.instContinuousFunctionalCalculus_isStarNormal`: `E →L[ℂ] E` carries a
  continuous functional calculus over the star-normal predicate.

-/

@[expose] public section

section

/-- The continuous functional calculus for star-normal continuous linear operators on a complex
Hilbert space. This is a global-instance promotion of the generic
`IsStarNormal.instContinuousFunctionalCalculus` theorem, specialized to the operator algebra
`E →L[ℂ] E`. -/
instance ContinuousLinearMap.instContinuousFunctionalCalculus_isStarNormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    ContinuousFunctionalCalculus ℂ (E →L[ℂ] E) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

end
