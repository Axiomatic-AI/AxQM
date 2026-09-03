/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.EntropyExchange
public import AxQM.ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropyConcave

/-! # Concavity of the entropy exchange in the quantum operation (Nielsen & Chuang, Exercise 12.13)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 12.13 asks one to show
that the **entropy exchange `S(ρ, E)` is concave in the quantum operation `E`**: for a convex
combination `E = p E₁ + (1 − p) E₂` of two trace-preserving quantum operations,
`p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, E)`.

## Main results

* `ContinuousLinearMap.channelMix` — the element family of the mixture `p E₁ + (1 − p) E₂`.
* `ContinuousLinearMap.entropyExchange_channelMix_ge` — **concavity of the entropy exchange**,
  `p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, p E₁ + (1 − p) E₂)` (Nielsen & Chuang, Exercise 12.13).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (entropy exchange), Exercise 12.13; §8.4.1 (mixing quantum operations).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct ComplexConjugate ComplexOrder
open InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ιb ι κ : Type*} [Fintype ιb]

/-- **The operation-element family of the mixture `p E₁ + (1 − p) E₂`** of two quantum operations
(Nielsen & Chuang §8.4.1). -/
noncomputable def channelMix (p : ℝ) (E₁ : ι → H →L[ℂ] H) (E₂ : κ → H →L[ℂ] H) :
    ι ⊕ κ → H →L[ℂ] H :=
  Sum.elim (fun i => (Real.sqrt p : ℂ) • E₁ i) (fun j => (Real.sqrt (1 - p) : ℂ) • E₂ j)

/-- **Concavity of the entropy exchange in the quantum operation** (Nielsen & Chuang, Exercise
12.13).

`p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, p E₁ + (1 − p) E₂)`.
-/
theorem entropyExchange_channelMix_ge [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : OrthonormalBasis ιb ℂ H) {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) (E₁ : ι → H →L[ℂ] H)
    (E₂ : κ → H →L[ℂ] H) (htp₁ : ∑ i, adjoint (E₁ i) * E₁ i = 1)
    (htp₂ : ∑ j, adjoint (E₂ j) * E₂ j = 1) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * entropyExchange ρ E₁ + (1 - p) * entropyExchange ρ E₂
      ≤ entropyExchange ρ (channelMix p E₁ E₂) := sorry

end ContinuousLinearMap
