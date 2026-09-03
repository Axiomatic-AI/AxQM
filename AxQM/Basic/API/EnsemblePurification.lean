/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# AxQM — purification of an ensemble's density operator

Nielsen–Chuang **Exercise 2.82(1)** (and the analogous construction of eq. (2.207)): given an
ensemble `{pᵢ, |ψᵢ⟩}` of a system `S` generating `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, and a reference system `R`
with orthonormal basis `|i⟩`, the vector `∑ᵢ √pᵢ |ψᵢ⟩|i⟩` purifies `ρ`.

## Main definitions

* `AxQM.Ensemble.purifyVec` — the raw purification vector `∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`.
* `AxQM.Ensemble.purify` — the purification as a `PureState` on
  `S ⊗ ofModel (EuclideanSpace ℂ (Fin e.card))`; unit norm is inherited from
  `TensorProduct.norm_eq_one_of_isPurification`.

## Main results

* `AxQM.Ensemble.purify_reducedLeft` — **Exercise 2.82(1)**, form: the left
  marginal of `|AR⟩⟨AR|` is `ρ`, i.e. `e.purify.toState.reducedLeft = e.toState`.
* The `*_ofOrthonormalBasis_onRight` family — **Exercise 2.82(2)/(3)** engine: measuring the
  reference in *any* orthonormal basis `b` recovers the ensemble whenever
  `φ.vec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i`.
  Its standard-basis case (`b = |i⟩`) is Exercise 2.82(2) (the `refMeasurement_*` corollaries) and
  its rotated-basis case is Exercise 2.82(3)
  (`exists_orthonormalBasis_refMeasurement_recovers_ensemble`).
-/

open scoped InnerProductSpace TensorProduct
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- The **ensemble purification vector** `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` (Nielsen–Chuang Exercise
2.82(1)): the subnormalized ensemble states `√pᵢ |ψᵢ⟩` tensored against the standard orthonormal
basis `|i⟩` of the reference `EuclideanSpace ℂ (Fin e.card)`. -/
def purifyVec (e : Ensemble S) :
    (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space :=
  ∑ i, (Real.sqrt (e.prob i) : ℂ) •
    ((e.states i).vec ⊗ₜ[ℂ] (EuclideanSpace.basisFun (Fin e.card) ℂ) i)

/-- **The ensemble purification vector purifies `ρ`**: the right-partial-trace of `|AR⟩⟨AR|`
recovers the ensemble's density operator `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`. -/
theorem isPurification_purifyVec (e : Ensemble S) :
    TensorProduct.IsPurification e.toState.op e.purifyVec := by
  have hpt := LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
      (fun i => Real.sqrt (e.prob i)) (fun i => (e.states i).vec)
      (fun i => (EuclideanSpace.basisFun (Fin e.card) ℂ) i)
      (EuclideanSpace.basisFun (Fin e.card) ℂ).orthonormal (Ψ := e.purifyVec) rfl
  unfold TensorProduct.IsPurification
  rw [hpt, e.toState_op, ContinuousLinearMap.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [ContinuousLinearMap.coe_smul, PureState.toState_op]
  congr 1
  norm_cast
  exact congrArg _ (Real.sq_sqrt (e.prob_nonneg i))

/-- **Ensemble purification** (Nielsen–Chuang Exercise 2.82(1), eq. (2.207)): the pure state on the
composite `S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))` whose vector is `∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`.
Unit norm is `TensorProduct.norm_eq_one_of_isPurification` applied to `isPurification_purifyVec`. -/
def purify (e : Ensemble S) :
    PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))) where
  vec := e.purifyVec
  normalized :=
    TensorProduct.norm_eq_one_of_isPurification e.toState.isDensity e.isPurification_purifyVec

/-- **Exercise 2.82(1): the ensemble purification has `ρ` as its left marginal.** Tracing out the
reference `R` of `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` recovers the ensemble's density operator:
`e.purify.toState.reducedLeft = e.toState`. -/
theorem purify_reducedLeft (e : Ensemble S) :
    e.purify.toState.reducedLeft = e.toState := sorry

/-- The **reference measurement** `Rᵢ = I_A ⊗ |i⟩⟨i|` (Nielsen–Chuang Exercise 2.82(2)): measure the
reference `R` in its standard basis `|i⟩`. -/
def refMeasurement (e : Ensemble S) :
    Measurement (Fin e.card) (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))) :=
  (Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin e.card) ℂ)).onRight S

/-- **Exercise 2.82(2), Born probability.** -/
theorem bornProb_refMeasurement_purify (e : Ensemble S) (i : Fin e.card) :
    e.refMeasurement.bornProb e.purify.toState i = e.prob i := sorry

/-- **Exercise 2.82(2), post-measurement state of `A`.** -/
theorem postMeasurement_refMeasurement_purify_reducedLeft (e : Ensemble S) (i : Fin e.card)
    (hp : e.refMeasurement.bornProb e.purify.toState i ≠ 0) :
    (e.refMeasurement.postMeasurement e.purify.toState i hp).reducedLeft
      = (e.states i).toState := sorry

/-- **Exercise 2.82(3): every purification's reference can be measured to recover the ensemble.**
Let `|AR⟩` (`φ`) be *any* purification of `ρ` to `S ⊗ R`, `R = ofModel (EuclideanSpace ℂ (Fin
e.card))` — a pure state of `S ⊗ R` with `Tr_R |AR⟩⟨AR| = ρ` (`φ.toState.reducedLeft = e.toState`).
Then there is an orthonormal basis `b` of `R` such that the projective measurement of `R` in `b`
(the composite `I_A ⊗ |bᵢ⟩⟨bᵢ|`) yields outcome `i` with probability `pᵢ` and collapses `A` to
`|ψᵢ⟩⟨ψᵢ|`.

Mathlib lemma). -/
theorem exists_orthonormalBasis_refMeasurement_recovers_ensemble (e : Ensemble S)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.toState.reducedLeft = e.toState) :
    ∃ b : OrthonormalBasis (Fin e.card) ℂ
        (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space,
      (∀ i, ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i = e.prob i) ∧
        ∀ i (hp : ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i ≠ 0),
          (((Measurement.ofOrthonormalBasis b).onRight S).postMeasurement
              φ.toState i hp).reducedLeft = (e.states i).toState := sorry

end Ensemble

end AxQM
