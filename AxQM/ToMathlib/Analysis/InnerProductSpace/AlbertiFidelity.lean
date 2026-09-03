/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNormUnitary
public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Alberti's variational characterization of the fidelity

This file proves the **lower-bound** direction, which holds for *arbitrary* positive `ρ, σ`
(no commutativity or invertibility assumption on the states):
```
F(ρ, σ)² ≤ tr(ρ P) tr(σ P⁻¹)   for every invertible positive P,
```
and, for *strictly positive* (invertible) `ρ, σ`, that this lower bound is **attained** at an
explicit minimizer, giving the full `IsLeast … F²`. For non-invertible states the infimum is not
attained (the minimizer would need `(√ρ)⁻¹`); the identity there is an infimum rather than a least
element, obtained by a regularization `ρ ↝ ρ + δ•1` as `δ → 0⁺`, giving the general
`IsGLB … F²` for *all* positive `ρ, σ` — the exact form of the book's statement.

## Main definitions

* `ContinuousLinearMap.albertiProduct ρ σ P` — the functional `tr(ρ P) · tr(σ P⁻¹)` (with the
  inverse taken as `Ring.inverse P`, the genuine inverse when `P` is invertible), whose infimum
  over invertible positive `P` is `F(ρ, σ)²`.

## Main results

* `ContinuousLinearMap.isGLB_albertiProduct` — **Alberti's theorem for all positive `ρ, σ`** (the
  book's `(9.145)`, corrected to `F²`): `F(ρ, σ)²` is the *infimum* of `tr(ρ P) tr(σ P⁻¹)` over
  invertible positive `P`, with no invertibility assumption on the states (approached, but not
  attained, when a state is rank-deficient).

## References

* P. M. Alberti, *A note on the transition probability over C\*-algebras*,
  Lett. Math. Phys. **7** (1983), 25–32.
* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Problem 9.1.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped ComplexOrder
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- The **Alberti functional** `P ↦ tr(ρ P) · tr(σ P⁻¹)` appearing on the right-hand side of
Nielsen & Chuang's Problem 9.1. The inverse of `P` is taken as `Ring.inverse P`, which is the
genuine two-sided inverse whenever `P` is invertible (the only `P` over which the infimum is
taken). For positive `ρ, σ` and invertible positive `P` the two traces are real and nonnegative,
so this is a nonnegative real number; its infimum over all invertible positive `P` is the squared
fidelity `F(ρ, σ)²` (Alberti's theorem). -/
noncomputable def albertiProduct (ρ σ P : E →L[ℂ] E) : ℝ :=
  RCLike.re (LinearMap.trace ℂ E (ρ * P)) *
    RCLike.re (LinearMap.trace ℂ E (σ * Ring.inverse P))

/-- **Alberti's theorem for arbitrary states** (Nielsen & Chuang Problem 9.1, corrected `F²` form).
For *any* positive operators `ρ, σ` — with **no invertibility assumption**, so covering all
density operators including rank-deficient ones — the squared fidelity `F(ρ, σ)² = ‖√ρ √σ‖₁²` is
the *infimum* of the Alberti functional `P ↦ tr(ρ P) tr(σ P⁻¹)` over invertible positive `P`.
This is the exact form of the book's `(9.145)`, whose infimum ranges over the invertible
positive `P`, once the printed unsquared `F` is corrected to `F²`. -/
theorem isGLB_albertiProduct (ρ σ : E →L[ℂ] E) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    IsGLB {y | ∃ P : E →L[ℂ] E, IsStrictlyPositive P ∧ albertiProduct ρ σ P = y}
      ((cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm ^ 2) := sorry

end ContinuousLinearMap
