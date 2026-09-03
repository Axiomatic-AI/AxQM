/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Eigenstate
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# AxQM.Basic.API — variance and standard deviation of an observable

The *statistics* of an observable in a pure state, built on
`PureState.expectation`. N&C, §2.2.5 (page 88) reads these off a
projective measurement of the observable `M`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Square of an observable** `M²`: the observable of the same system with operator `M.op ^ 2`.
The observable measured when computing the mean square value `⟪M²⟫`. -/
def Observable.sq (A : Observable S) : Observable S where
  op := A.op ^ 2
  selfAdjoint := A.selfAdjoint.pow 2

namespace PureState

/-- **Variance** `[Δ(M)]²_ψ = ⟪M²⟫_ψ − ⟪M⟫_ψ²` of an observable `A` in the pure state `ψ`
(N&C (2.115)): the mean square spread of the measured values of `A`. -/
def variance (ψ : PureState S) (A : Observable S) : ℝ :=
  ψ.expectation A.sq - (ψ.expectation A) ^ 2

/-- **Standard deviation** `Δ(M)_ψ = √(⟪M²⟫_ψ − ⟪M⟫_ψ²)` of an observable `A` in the pure state `ψ`
(N&C, page 88): the square root of the variance, measuring the typical spread of the observed
values of `A`. -/
def stdDev (ψ : PureState S) (A : Observable S) : ℝ := Real.sqrt (ψ.variance A)

end PureState

end AxQM
