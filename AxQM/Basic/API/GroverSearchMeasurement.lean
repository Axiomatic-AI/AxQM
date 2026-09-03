/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.GroverSearchIterations
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.ProjectiveMeasurement

/-!
# AxQM.Basic.API — measuring the Grover search state

The **physical** step of the quantum search algorithm: after `R` Grover iterations one *measures*
the register in the computational basis and reads off a solution.

## Contents

* `groverFinalState θ R` — the state **after `R` Grover iterations**, `Gᴿ|ψ⟩`, as a `PureState` of
  the qubit `span{|α⟩,|β⟩}`; its vector is the algorithm's output
  `(groverIteration θ)^R *ᵥ groverState θ`.
* `groverSolutionMeasurement` — the two-outcome projective measurement of the reduced qubit in the
  `{|α⟩, |β⟩}` basis. Outcome `0` is `|α⟩` (a *non*-solution), outcome `1` is `|β⟩` (a *solution*):
  it is the coarse-graining "did the computational-basis measurement return a solution?" of N&C's
  full `n`-qubit measurement, since `|β⟩` is the unit vector spanning exactly the solution outcomes.
-/

open scoped InnerProductSpace
open Matrix

noncomputable section

namespace AxQM

open Concrete

/-- **The Grover search state after `R` iterations**, `Gᴿ|ψ⟩`, as a `PureState` of the reduced
qubit `span{|α⟩, |β⟩}`. -/
def groverFinalState (θ : ℝ) (R : ℕ) : PureState qubit where
  vec := WithLp.toLp 2 ((groverIteration θ) ^ R *ᵥ groverState θ)
  normalized := by
    rw [groverIteration_pow_mulVec_groverState]
    change ‖(WithLp.toLp 2 (planeState ((2 * (R : ℝ) + 1) * θ / 2)) :
        EuclideanSpace ℂ (Fin 2))‖ = 1
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [planeState_apply_zero, planeState_apply_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have hpyth : Real.cos ((2 * (R : ℝ) + 1) * θ / 2) ^ 2
        + Real.sin ((2 * (R : ℝ) + 1) * θ / 2) ^ 2 = 1 :=
      by linear_combination Real.sin_sq_add_cos_sq ((2 * (R : ℝ) + 1) * θ / 2)
    rw [hpyth, Real.sqrt_one]

/-- **The projective measurement of the reduced qubit in the `{|α⟩, |β⟩}` basis**. Outcome
`0` is `|α⟩` — a non-solution — and outcome `1` is `|β⟩` — a solution. This is the coarse-graining
"did we measure a solution?" of the full `n`-qubit computational-basis measurement of the quantum
search algorithm (N&C's step 4), since `|β⟩` is the unit vector spanning exactly the solution
outcomes. -/
def groverSolutionMeasurement : Measurement (Fin 2) qubit :=
  Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin 2) ℂ)

end AxQM
