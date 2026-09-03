/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Mixture
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# AxQM — the von Neumann entropy along a mixing line, and the second-derivative
concavity criterion (Nielsen & Chuang Exercise 11.22, Part 1)

Nielsen & Chuang **Exercise 11.22** ("Alternate proof of concavity", §11.3.5, p. 518) concerns the
entropy along the mixing line between two states `ρ, σ`.

## Main definitions

* `AxQM.State.entropyMixLine` — the function `f(p) = S(p ρ + (1 − p) σ)`.

## Main results

* `AxQM.State.vonNeumannEntropy_concave_of_deriv2_nonpos` — the sufficiency reduction:
  `f'' ≤ 0` (with smoothness) gives the two-point concavity inequality.
-/

namespace AxQM

variable {S : QSystem}

/-- The **von Neumann entropy along the mixing line** through two states `ρ, σ`: `f(p) = S(p ρ + (1
− p) σ)` (Nielsen & Chuang Exercise 11.22). -/
noncomputable def State.entropyMixLine (ρ σ : State S) (p : ℝ) : ℝ :=
  ((p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op).vonNeumannEntropy

/-- **N&C Exercise 11.22, Part 1 — concavity from `f''(p) ≤ 0`.**
Combining the two reduction steps: if the mixing-line entropy `f(p) = S(p ρ + (1 − p) σ)` has
non-positive second derivative on `(0,1)` (with the packaged smoothness), then the two-point
concavity inequality holds: for `0 ≤ p ≤ 1`,

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`.

The hypothesis `f''(p) ≤ 0` is assumed rather than derived: it requires the parametric
derivative of the operator logarithm. -/
theorem State.vonNeumannEntropy_concave_of_deriv2_nonpos {ρ σ : State S}
    (hcont : ContinuousOn (ρ.entropyMixLine σ) (Set.Icc 0 1))
    (hdiff : DifferentiableOn ℝ (ρ.entropyMixLine σ) (interior (Set.Icc 0 1)))
    (hdiff2 : DifferentiableOn ℝ (deriv (ρ.entropyMixLine σ)) (interior (Set.Icc 0 1)))
    (hf2 : ∀ p ∈ interior (Set.Icc (0 : ℝ) 1), (deriv^[2] (ρ.entropyMixLine σ)) p ≤ 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy
      ≤ (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy := sorry

/-- **Exercise 11.22, Part 2 (invertible case): `f''(p) ≤ 0`.** For invertible states `ρ, σ`. -/
theorem State.entropyMixLine_deriv2_nonpos_of_isStrictlyPositive {ρ σ : State S}
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (deriv^[2] (ρ.entropyMixLine σ)) p ≤ 0 := sorry

end AxQM
