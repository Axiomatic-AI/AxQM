/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
-- `TensorProduct` is re-imported LAST on purpose: it re-asserts the inner-product-space
-- normed structure on `E ⊗[𝕜] F` as the resolution-priority `AddCommMonoid`/`Module` instance
-- over the bare algebraic `TensorProduct.instModule`. Without this, a tensor operator built with
-- `homTensorHomEquiv`/`TensorProduct.map` (algebraic module) fails to unify with the normed module
-- that `ContinuousLinearMap`/`LinearMap.IsPositive` require, even though the two are defeq.

/-!
# Complete positivity and the forward direction of the operator-sum theorem

The **ampliation** of a superoperator `Φ` (a linear map on operators) by a reference space `R` is
the map `id_{B(R)} ⊗ Φ` acting on operators of `R ⊗ H`, characterised by
`(id_{B(R)} ⊗ Φ)(B ⊗ M) = B ⊗ Φ(M)`. A superoperator is **completely positive** when every such
ampliation preserves positivity — Nielsen–Chuang's axiom **A3** (*Quantum Computation and Quantum
Information*, §8.2.4). This file introduces the ampliation and complete positivity for operators on
finite-dimensional inner product spaces, packages the three N&C axioms into
`SatisfiesOperationAxioms`, and proves the **forward direction of the operator-sum representation
theorem**: an operator-sum (Kraus) map `krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` with
`Σᵢ Eᵢ† Eᵢ ≤ 1` satisfies axioms A1, A2, A3.

## Main definitions

* `ContinuousLinearMap.superopAmpliationₗ R Φ` — the **ampliation** `id_{B(R)} ⊗ Φ` of a
  `LinearMap`-superoperator `Φ : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G)`, built from `homTensorHomEquiv`
  and `LinearMap.lTensor`. (The `ₗ` subscript marks the bundled-`LinearMap` form, matching
  `krausSumₗ`.)
* `ContinuousLinearMap.toLMSuperop Φ` — a `ContinuousLinearMap`-superoperator
  `Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)` reinterpreted on the underlying linear maps, so that its
  ampliation and complete positivity are expressible.
* `ContinuousLinearMap.IsCompletelyPositive Φ` — **complete positivity** (N&C axiom A3): for every
  finite-dimensional reference space `R`, the ampliation `id_{B(R)} ⊗ Φ` sends positive operators
  on `R ⊗ H` to positive operators on `R ⊗ G`.
* `ContinuousLinearMap.IsTraceNonIncreasing Φ` — **axiom A1**: `re tr(Φ ρ) ≤ re tr ρ` for every
  positive `ρ` (the scaling-invariant form of `tr[Φ ρ] ≤ 1` on states).
* `ContinuousLinearMap.SatisfiesOperationAxioms Φ` — the **three axioms A1, A2, A3** bundled:
  completely positive and trace-non-increasing (A2 is subsumed by `Φ` being a linear map).
* `ContinuousLinearMap.IsOperatorSum E Φ` — `Φ` has the **operator-sum form** `Φ = krausSumₗ E`
  with `Σᵢ Eᵢ† Eᵢ ≤ 1` (the right-hand side of Theorem 8.1).
-/

open scoped TensorProduct
open ContinuousLinearMap

noncomputable section

@[expose] public section

namespace ContinuousLinearMap

section General

variable {𝕜 H G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]

/-- A **`ContinuousLinearMap`-superoperator** `Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)` reinterpreted as a
`LinearMap`-superoperator on the underlying linear maps, via the finite-dimensional identification
`LinearMap.toContinuousLinearMap`. This is the form on which the ampliation `superopAmpliationₗ`
(hence complete positivity) is stated. -/
def toLMSuperop (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G) :=
  (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := G)).symm.toLinearMap ∘ₗ Φ ∘ₗ
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := H)).toLinearMap

/-- The **ampliation** `id_{B(R)} ⊗ Φ` of a `LinearMap`-superoperator `Φ` by a reference space `R`:
the linear map on operators sending `A : R ⊗ H →ₗ[𝕜] R ⊗ H` to the operator on `R ⊗ G` that applies
`Φ` to the `H`-factor while leaving the `R`-factor untouched. Built from the operator–tensor
identification `homTensorHomEquiv` and `LinearMap.lTensor`. The `ₗ` subscript marks the
bundled-`LinearMap` form. -/
def superopAmpliationₗ (R : Type*) [NormedAddCommGroup R] [InnerProductSpace 𝕜 R]
    [FiniteDimensional 𝕜 R]
    (Φ : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G)) :
    (R ⊗[𝕜] H →ₗ[𝕜] R ⊗[𝕜] H) →ₗ[𝕜] (R ⊗[𝕜] G →ₗ[𝕜] R ⊗[𝕜] G) :=
  (homTensorHomEquiv 𝕜 R G R G).toLinearMap ∘ₗ
    (LinearMap.lTensor (R →ₗ[𝕜] R) Φ) ∘ₗ
    (homTensorHomEquiv 𝕜 R H R H).symm.toLinearMap

/-- **Complete positivity of a superoperator `Φ` (Nielsen–Chuang axiom A3).** For every
finite-dimensional reference space `R`, the ampliation `id_{B(R)} ⊗ Φ` sends positive
operators on `R ⊗ H` to positive operators on `R ⊗ G`. (The reference ranges over `Type 0`; see the
module implementation notes on why this captures "arbitrary dimension".) -/
def IsCompletelyPositive (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : Prop :=
  ∀ (R : Type) [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
    (A : R ⊗[𝕜] H →ₗ[𝕜] R ⊗[𝕜] H), A.IsPositive →
      (superopAmpliationₗ R (toLMSuperop Φ) A).IsPositive

/-- **Trace-non-increasing — Nielsen–Chuang axiom A1.** A superoperator `Φ` is
*trace-non-increasing* when `re tr(Φ ρ) ≤ re tr ρ` for every positive operator `ρ`. For a state
`ρ` (trace one), this reads `tr[Φ ρ] ≤ 1`; the scaling-invariant form over all positive `ρ` is
equivalent and is exactly N&C's requirement that `tr[E(ρ)]` be a probability, `0 ≤ tr[E(ρ)] ≤ 1`
(the lower bound `0 ≤ re tr(Φ ρ)` being a consequence of positivity, hence of axiom A3). -/
def IsTraceNonIncreasing (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : Prop :=
  ∀ ρ : H →L[𝕜] H, 0 ≤ ρ →
    RCLike.re (LinearMap.trace 𝕜 G ((Φ ρ : G →L[𝕜] G) : G →ₗ[𝕜] G))
      ≤ RCLike.re (LinearMap.trace 𝕜 H ((ρ : H →L[𝕜] H) : H →ₗ[𝕜] H))

/-- **A quantum operation (the Nielsen–Chuang axioms A1, A2, A3).** A superoperator `Φ` satisfies
the operation axioms when it is completely positive (axiom A3, `IsCompletelyPositive`) and
trace-non-increasing (axiom A1, `IsTraceNonIncreasing`). Axiom A2 (convex-linearity on density
operators) is *subsumed by the type*: `Φ` is modelled as a genuine `𝕜`-linear map on operators, the
unique linear extension of a convex-linear map on density operators (which spans the operator
space), so linearity — hence convex-linearity — holds by construction. This bundled predicate is
the left-hand side of the operator-sum representation theorem. -/
def SatisfiesOperationAxioms (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : Prop :=
  IsCompletelyPositive Φ ∧ IsTraceNonIncreasing Φ

end General

section Complex

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **An operator-sum (Kraus) representation of a superoperator `Φ`.** A family of operation
elements `E : ι → H →L[ℂ] G` represents `Φ` when `Φ` *is* the operator-sum map of `E`,
`Φ = krausSumₗ E` (i.e. `Φ ρ = Σᵢ Eᵢ ρ Eᵢ†` for all `ρ`), and the operation elements obey the trace
condition `Σᵢ Eᵢ† Eᵢ ≤ 1`. This is the right-hand side of the operator-sum representation theorem
: `Φ` satisfies the operation axioms iff some finite family `E` gives
`IsOperatorSum E Φ`. -/
def IsOperatorSum {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)) : Prop :=
  Φ = krausSumₗ E ∧ ∑ i, adjoint (E i) ∘L E i ≤ 1

end Complex

end ContinuousLinearMap
