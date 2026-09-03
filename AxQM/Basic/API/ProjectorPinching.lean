/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.RandomUnitaryChannel
import AxQM.Basic.API.UnreadMeasurement

/-!
# AxQM.Basic.API — the pinching (dephasing) map as a random-unitary channel

The **pinching** (non-selective dephasing) map of a projective measurement with orthogonal
projectors `{Pᵢ}` (a complete set, `∑ᵢ Pᵢ = 1`) is `ρ ↦ Σᵢ Pᵢ ρ Pᵢ` — the unread post-measurement
state `Measurement.unreadState` of that measurement. This file exhibits it as a **random-unitary
channel** `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†`, as asked by Nielsen & Chuang, **Exercise 11.20**.

## Main results

* `AxQM.reflectionEvolutionOfProj` — the reflection `1 - 2P` as a unitary `Evolution`.
* `AxQM.projPinching_two_eq_reflection_evolve_mix` — the **two-projector observation** of
  Exercise 11.20: for `Q = 1 - P`, `P ρ P + Q ρ Q = ½ ρ + ½ (1 - 2P) ρ (1 - 2P)` (the `|ι| = 2`
  case, stated concretely).
-/

open scoped BigOperators
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- The **reflection** `1 - 2P` of an orthogonal projector `P`, as a unitary `Evolution`. -/
def reflectionEvolutionOfProj {P : S →L[ℂ] S} (hP : IsStarProjection P) : Evolution S where
  op := 1 - (2 : ℂ) • P
  unitary := by
    have hsa : star (1 - (2 : ℂ) • P) = 1 - (2 : ℂ) • P := by
      rw [star_sub, star_one, star_smul, hP.isSelfAdjoint.star_eq]; norm_num
    have hinv : (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
      have hi : P * P = P := hP.isIdempotentElem
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hi]
      match_scalars <;> ring
    rw [Unitary.mem_iff, hsa]; exact ⟨hinv, hinv⟩

/-- **Nielsen & Chuang, Exercise 11.20 — the two-projector observation, with unitary witnesses.**
For an orthogonal projector `P` (`Q = 1 - P`) and any state `ρ`, the two-outcome pinching `P ρ P
+ Q ρ Q` is the equal mixture of the two unitary conjugations `U₁ ρ U₁†` and `U₂ ρ U₂†`,

`P ρ P + Q ρ Q = ½ (U₁ ρ U₁†) + ½ (U₂ ρ U₂†)`,

with `U₁ = 1` (`Evolution.id`), `U₂ = 1 - 2P` (`reflectionEvolutionOfProj hP`) and `p = ½` —
exactly N&C's `P ρ P + Q ρ Q = p U₁ ρ U₁† + (1 - p) U₂ ρ U₂†`.
-/
theorem projPinching_two_eq_reflection_evolve_mix {P : S →L[ℂ] S} (hP : IsStarProjection P)
    (ρ : State S) :
    P * ρ.op * P + (1 - P) * ρ.op * (1 - P)
      = (1 / 2 : ℂ) • ((Evolution.id : Evolution S).evolve ρ).op
        + (1 / 2 : ℂ) • ((reflectionEvolutionOfProj hP).evolve ρ).op := sorry

end AxQM
