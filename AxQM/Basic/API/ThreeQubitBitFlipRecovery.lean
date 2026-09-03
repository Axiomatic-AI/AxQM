/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ThreeQubitBitFlipCode
import AxQM.Basic.API.QuditMeasurement
import AxQM.Basic.API.PeriodShift
import AxQM.Basic.API.ProjectiveRecovery

/-!
# AxQM.Basic.API — the eight-projector recovery of the three-qubit bit-flip code

Nielsen & Chuang, Exercise 10.4 asks what happens when the syndrome measurement of the
three-qubit bit-flip code is performed with the **eight rank-one computational-basis
projectors** `|x⟩⟨x|` (`x : Fin 8`) instead of the four commuting syndrome projectors. This
file defines that recovery as a `ProjectiveUnitaryRecovery`, and the encoded logical qubit
`a|0_L⟩ + b|1_L⟩`.
-/

open scoped InnerProductSpace
open AxQM.Concrete InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The eight-projector recovery of the three-qubit bit-flip code** (Nielsen & Chuang, Exercise
10.4): the projective-measurement-then-conditional-unitary recovery whose

* syndrome measurement is the eight-projector computational-basis measurement `quditMeasurement 8`
  (outcome `x` the rank-one projector `|x⟩⟨x|`), and
* conditional correction on outcome `x` is the recovery flip
  `quditPerm (xorPerm (errorMask (syndrome x)))` — the permutation gate that re-applies the
  single-qubit error diagnosed by the majority-vote `syndrome x`. -/
def bitFlipRecovery : ProjectiveUnitaryRecovery (Fin 8) (qudit 8) where
  meas := quditMeasurement 8
  proj := fun i => by
    rw [quditMeasurement_op]
    exact isStarProjection_rankOne_self (quditBasis i).normalized
  corr x := quditPerm (xorPerm (errorMask (syndrome x)))

/-- **The encoded logical qubit** `a|0_L⟩ + b|1_L⟩ = a|000⟩ + b|111⟩` of the three-qubit
bit-flip code, as the pure state `a•|0⟩ + b•|7⟩` of `qudit 8`, for amplitudes with
`‖a‖² + ‖b‖² = 1`. The two logical basis codewords are
`encodedCodeState 1 0` (`|0_L⟩`) and `encodedCodeState 0 1` (`|1_L⟩`); a genuine superposition
has `a ≠ 0` and `b ≠ 0`. -/
def encodedCodeState (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : PureState (qudit 8) where
  vec := a • (quditBasis 0).vec + b • (quditBasis 7).vec
  normalized := by
    set v : (qudit 8).space := a • (quditBasis 0).vec + b • (quditBasis 7).vec with hv
    have horth : inner ℂ (quditBasis (0 : Fin 8)).vec (quditBasis (7 : Fin 8)).vec = 0 := by
      rw [quditBasis_inner, if_neg (by decide)]
    have hcross : RCLike.re (inner ℂ (a • (quditBasis (0 : Fin 8)).vec)
        (b • (quditBasis (7 : Fin 8)).vec)) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero, map_zero]
    have hsq : ‖v‖ ^ 2 = 1 := by
      rw [hv, norm_add_sq (𝕜 := ℂ), hcross, norm_smul, norm_smul, (quditBasis 0).normalized,
        (quditBasis 7).normalized, mul_one, mul_one, mul_zero, add_zero]
      exact h
    rw [← Real.sqrt_sq (norm_nonneg v), hsq, Real.sqrt_one]

end AxQM
