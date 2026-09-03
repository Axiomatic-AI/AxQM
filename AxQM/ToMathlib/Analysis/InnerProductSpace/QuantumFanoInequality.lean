/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.EntropyExchange
public import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import AxQM.ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropy

/-! # The quantum Fano inequality

For a state `ρ` (a density operator on a `d`-dimensional complex inner product space `H`, so
`d = finrank ℂ H`) and a trace-preserving quantum operation with operation elements
`E : ι → (H →L[ℂ] H)` (`∑ᵢ Eᵢ† Eᵢ = 1`), the **entropy exchange** `S(ρ, E)` and the **entanglement
fidelity** `F(ρ, E)` obey the **quantum Fano inequality** (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, Theorem 12.9, eq. (12.112)):
`S(ρ, E) ≤ H(F(ρ, E)) + (1 - F(ρ, E)) · log (d² - 1)`,
where `H` is the binary Shannon entropy.

## Main results

* `ContinuousLinearMap.entropyExchange_le_binEntropy_entanglementFidelity_add` — the quantum Fano
  inequality `S(ρ, E) ≤ H(F(ρ, E)) + (1 - F(ρ, E)) · log (d² - 1)` (N&C Theorem 12.9, eq. (12.112)).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (Theorem 12.9, eqs. (12.107)–(12.115)).
-/

open scoped InnerProductSpace TensorProduct ComplexConjugate
open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The quantum Fano inequality** (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 12.9, eq. (12.112)). For a density operator `ρ` on a `d`-dimensional space
`H` (`d = finrank ℂ H`) and a trace-preserving quantum operation with operation elements `E : ι
→ (H →L[ℂ] H)` (`∑ᵢ Eᵢ† Eᵢ = 1`), the entropy exchange is bounded by the binary Shannon entropy
of the entanglement fidelity: `S(ρ, E) ≤ H(F(ρ, E)) + (1 - F(ρ, E)) · log (d² - 1)`.
-/
theorem entropyExchange_le_binEntropy_entanglementFidelity_add
    {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) {E : ι → H →L[ℂ] H}
    (htp : ∑ i, adjoint (E i) * E i = 1) :
    entropyExchange ρ E ≤ Real.binEntropy (entanglementFidelity ρ E)
      + (1 - entanglementFidelity ρ E) * Real.log ((Module.finrank ℂ H : ℝ) ^ 2 - 1) := sorry

end ContinuousLinearMap
