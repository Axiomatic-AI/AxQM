/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.StateDiscrimination

/-!
# AxQM.Basic.API — unambiguous state discrimination by a POVM

The physics wrapper for Nielsen & Chuang, Exercise 2.64: given a family of **pure states**
`ψ : ι → PureState S` whose underlying vectors are linearly independent, there is a POVM whose
informative outcomes discriminate them *with certainty*.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Discriminating POVM (N&C Exercise 2.64).** For a family of pure states `ψ : ι → PureState S`,
the POVM on outcomes `Option ι` whose informative outcome `some i` detects state `ψ i` and whose
outcome `none` is inconclusive. It is the general `POVM.distinguishing` construction applied to
the state vectors `(ψ i).vec`. -/
def distinguishingPOVM (ψ : ι → PureState S) : POVM (Option ι) ℂ S.space :=
  POVM.distinguishing ℂ (fun i => (ψ i).vec)

/-- The Born-rule probability of the informative outcome `some i` on its own state `ψ i` is
strictly positive — Nielsen & Chuang's requirement `⟪ψᵢ, Eᵢ ψᵢ⟫ > 0`, ensuring the outcome can
actually occur for the intended state. Requires the state vectors to be linearly independent. -/
theorem distinguishingPOVM_prob_pos (ψ : ι → PureState S)
    (hψ : LinearIndependent ℂ (fun i => (ψ i).vec)) (i : ι) :
    0 < (distinguishingPOVM ψ).toPMF (ψ i).toState.op (some i) := sorry

/-- **Discrimination with certainty.** If the informative outcome `some i` has nonzero
probability on state `ψ j`, then `j = i`: observing `some i` identifies the input as `ψ i`. -/
theorem distinguishingPOVM_certain (ψ : ι → PureState S) {i j : ι}
    (h : (distinguishingPOVM ψ).toPMF (ψ j).toState.op (some i) ≠ 0) : j = i := sorry

end AxQM
