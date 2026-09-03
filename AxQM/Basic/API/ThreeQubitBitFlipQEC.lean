/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BitFlipSyndromeMeasurement
import AxQM.Basic.API.QuantumErrorCorrection

/-!
# AxQM.Basic.API — the QEC conditions for the three-qubit bit-flip code (N&C Ex 10.7)

Infrastructure for **Nielsen & Chuang, Exercise 10.7**: the three-qubit bit-flip code
of §10.1.1, with code projector `P = |000⟩⟨000| + |111⟩⟨111|` (`bitFlipSyndromeProj 0`), satisfies
the quantum error-correction conditions (N&C Thm 10.1, `SatisfiesQECConditions`) for the
*non-trace-preserving* noise process of the exercise.

## Contents

* `bitFlipX k` — the three single-qubit bit-flip errors `X₁, X₂, X₃` as tensor observables on
  `bitFlipReg`.
* `bitFlipErrorOp` — the unscaled error family `T = (I, X₁, X₂, X₃)`.
* `threeBitFlipNoise p` — the four noise operation elements.
* `threeBitFlipNoise_satisfiesQECConditions` — (N&C Ex 10.7) the QEC conditions hold.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The three single-qubit bit-flip errors** `X₁ = X⊗I⊗I`, `X₂ = I⊗X⊗I`, `X₃ = I⊗I⊗X` on the
three-qubit register `bitFlipReg`, as tensor observables (N&C's `X₁, X₂, X₃`). -/
def bitFlipX : Fin 3 → Observable bitFlipReg :=
  ![pauliXObservable ⊗ (Observable.id qubit ⊗ Observable.id qubit),
    Observable.id qubit ⊗ (pauliXObservable ⊗ Observable.id qubit),
    Observable.id qubit ⊗ (Observable.id qubit ⊗ pauliXObservable)]

/-- **The four unscaled error operators** `T = (I, X₁, X₂, X₃)` — the noise operation elements with
their scalar coefficients stripped off. -/
def bitFlipErrorOp : Fin 4 → bitFlipReg.space →L[ℂ] bitFlipReg.space :=
  ![1, (bitFlipX 0).op, (bitFlipX 1).op, (bitFlipX 2).op]

variable (p : ℝ)

/-- The real coefficients of the noise operation elements: `√(1−p)³` for no bit flip, `√(p(1−p)²)`
for each single bit flip. -/
def threeBitFlipNoiseCoeff : Fin 4 → ℝ :=
  ![Real.sqrt ((1 - p) ^ 3), Real.sqrt (p * (1 - p) ^ 2), Real.sqrt (p * (1 - p) ^ 2),
    Real.sqrt (p * (1 - p) ^ 2)]

/-- **The four noise operation elements** of N&C Ex 10.7: `E₀ = √(1−p)³ · I` (no bit flip) and
`Eₖ = √(p(1−p)²) · Xₖ` (a bit flip on qubit `k`), for `k = 1, 2, 3`. The two- and three-qubit bit
flips are omitted, so this is *not* trace-preserving. -/
def threeBitFlipNoise : Fin 4 → bitFlipReg.space →L[ℂ] bitFlipReg.space :=
  fun i => (threeBitFlipNoiseCoeff p i : ℂ) • bitFlipErrorOp i

/-- **Nielsen & Chuang, Exercise 10.7.** The three-qubit bit-flip code (code projector `P =
|000⟩⟨000| + |111⟩⟨111|`) satisfies the **quantum error-correction conditions**
(`SatisfiesQECConditions`, N&C Thm 10.1) for the non-trace-preserving noise process with
operation elements `{√(1−p)³ · I, √(p(1−p)²) · X₁, √(p(1−p)²) · X₂, √(p(1−p)²) · X₃}` (`0 ≤ p ≤
1`). -/
theorem threeBitFlipNoise_satisfiesQECConditions (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    SatisfiesQECConditions (bitFlipSyndromeProj 0) (threeBitFlipNoise p) := sorry

end AxQM
