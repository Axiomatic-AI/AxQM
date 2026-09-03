/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement

/-!
# AxQM — measurement as a quantum operation (N&C Exercise 8.2)

The underlying operator bridge realizing **Nielsen–Chuang Exercise 8.2**: a general measurement
(`Measurement`) acts on density operators as a quantum operation.

## Contents

* `Measurement.opElement` — the quantum operation element `Eₘ(ρ) = Mₘ ρ Mₘ†` of outcome `i`
  (a thin `AxQM`-level name for `ContinuousLinearMap.postOp m.op ρ.op i`).
* `Measurement.bornProb_eq_trace_opElement` — **Exercise 8.2, probability:** `p(m) = tr(Eₘ(ρ))`,
  as the equality `(p(m) : ℂ) = tr(Eₘ(ρ))` (the trace is real and equals the Born probability).
* `Measurement.postMeasurement_op_eq_opElement_div` — **Exercise 8.2, state update:** the
  post-measurement state is `Eₘ(ρ)/tr(Eₘ(ρ))` (N&C Eq. (8.5)).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **quantum operation element** of outcome `i` for the measurement `m` on state `ρ`:
`Eₘ(ρ) = Mₘ ρ Mₘ†` (Nielsen–Chuang Eq. (8.5)). A `AxQM`-level name for the operator-level
post-measurement operation `ContinuousLinearMap.postOp m.op ρ.op i`. -/
def opElement (m : Measurement ι S) (ρ : State S) (i : ι) : S →L[ℂ] S :=
  ContinuousLinearMap.postOp m.op ρ.op i

/-- **Nielsen & Chuang, Exercise 8.2 (outcome probability).** The probability of obtaining outcome
`i` is the trace of the quantum operation element: `p(m) = tr(Eₘ(ρ))`. Stated as the complex
equality `(p(m) : ℂ) = tr(Eₘ(ρ))`, which records both that `tr(Eₘ(ρ))` is real and that it
equals the Born probability `bornProb`. -/
theorem bornProb_eq_trace_opElement (m : Measurement ι S) (ρ : State S) (i : ι) :
    (m.bornProb ρ i : ℂ) = LinearMap.trace ℂ S (m.opElement ρ i : S →ₗ[ℂ] S) := sorry

/-- **Nielsen & Chuang, Exercise 8.2 (state update, Eq. (8.5)).** The state of the system
immediately after obtaining outcome `i` is `Eₘ(ρ)/tr(Eₘ(ρ))`: the quantum operation element
normalized by its trace. This is N&C's Equation (8.5). -/
theorem postMeasurement_op_eq_opElement_div (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) :
    (m.postMeasurement ρ i hp).op
      = (LinearMap.trace ℂ S (m.opElement ρ i : S →ₗ[ℂ] S))⁻¹ • m.opElement ρ i := sorry

end Measurement

end AxQM
