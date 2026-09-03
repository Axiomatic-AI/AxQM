/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorGram
public import AxQM.ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-! # Entropy exchange `S(ρ, E)` and the reference-system output state

For a state `ρ` (a density operator on a `d`-dimensional complex inner product space `H`) and a
finite family of operation elements `E : ι → (H →L[ℂ] H)` of a trace-preserving quantum operation,
Nielsen & Chuang define the **entropy exchange** (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, §12.4.1, eqs. (12.107)–(12.110)) by
`S(ρ, E) := S(R', Q') = S(W)`,
where `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` is the **`w`-matrix** — the density operator of the environment in the
Stinespring dilation, in the operation-element basis (eq. (12.109)) — and `S(W) = -tr(W log W)` is
its von Neumann entropy (eq. (12.110)).

## Main definitions

* `ContinuousLinearMap.wMatrix` — the `w`-matrix `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` (N&C eq. (12.109)–(12.110)).
* `ContinuousLinearMap.entropyExchange` — the entropy exchange `S(ρ, E) = S(W)` (N&C eq. (12.110)).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (eqs. (12.107)–(12.110), Theorem 12.9); §9.3 (Eq. (9.135)).
-/

open scoped InnerProductSpace TensorProduct ComplexConjugate
open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ιb ι : Type*} [Fintype ιb]

/-- The **`w`-matrix** `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` of a state `ρ` and a family of operation elements
`E : ι → (H →L[ℂ] H)` (Nielsen & Chuang, *Quantum Computation and Quantum Information*, eqs.
(12.109)–(12.110)). It is the matrix of the environment's density operator `ρ_{E'}` in the
operation-element basis of the Stinespring dilation; its von Neumann entropy is the entropy
exchange. -/
noncomputable def wMatrix (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) : Matrix ι ι ℂ :=
  fun j k => LinearMap.trace ℂ H ((E j * ρ * adjoint (E k) : H →L[ℂ] H) : H →ₗ[ℂ] H)

/-- The **entropy exchange** `S(ρ, E) = S(W) = -tr(W log W)` of a state `ρ` under a quantum
operation with operation elements `E` (Nielsen & Chuang, eq. (12.110)). Defined as the von Neumann
entropy of the operator on `EuclideanSpace ℂ ι` represented by the `w`-matrix `W = wMatrix ρ E`. -/
noncomputable def entropyExchange [Fintype ι] [DecidableEq ι] (ρ : H →L[ℂ] H)
    (E : ι → H →L[ℂ] H) : ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (wMatrix ρ E)).vonNeumannEntropy

end ContinuousLinearMap
