/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasurementOperation
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — reduced operation of a general measurement on system + environment (N&C Ex 8.7)

The machinery behind **Nielsen–Chuang Exercise 8.7**. In §8.2.4 a principal system
`Q` (state `ρ`) is adjoined to an environment `E` (state `σ`), the pair interacts via a unitary `U`,
and a measurement is performed on the *combined* system `Q ⊗ E`. Where N&C's worked derivation
(eqs. (8.29)–(8.35)) uses a **projective** measurement `{Pₘ}`, Exercise 8.7 replaces it with a
**general** measurement `{Mₘ}` (`∑ₘ Mₘ† Mₘ = 1`, our `Measurement` primitive) and asks for

## Contents

* `generalMeasurementEnvOp` — the induced operation `Eₘ(ρ) = tr_E(Mₘ (U (ρ ⊗ σ) U†) Mₘ†)`, as a
  `Q →L[ℂ] Q`.
* `bornProb_eq_trace_generalMeasurementEnvOp` — **Exercise 8.7 (probabilities):** the outcome
  probability equals the trace of the induced operation, `(p(m) : ℂ) = tr[Eₘ(ρ)]`. Stated as the
  complex equality (so the trace is real and equals the Born probability), for the general
  measurement `M` on the post-interaction joint state `U.evolve (ρ ⊗ σ)`.
* `generalMeasurementEnvKrausOp` — the operation elements `Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩` (N&C's
  `Eⱼₖ = √qⱼ ⟨eₖ| Mₘ U |j⟩` of Eq. (8.35), the weights absorbed into `wⱼ`).
* `generalMeasurementEnvOp_eq_sum_krausOp` — **Exercise 8.7 (operator-sum representation):** for an
  ensemble decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|`, `Eₘ(ρ) = ∑ⱼ ∑ₖ Eⱼₖ ρ Eⱼₖ†` (N&C Eqs. (8.33)–(8.35)).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {Q E : QSystem}

/-- **The induced quantum operation of a general measurement on system + environment** (Nielsen–
Chuang Exercise 8.7, eq. (8.32) with the projectors `Pₘ` replaced by general measurement
operators `Mₘ`):

`Eₘ(ρ) = tr_E( Mₘ (U (ρ ⊗ σ) U†) Mₘ† )`,

The inner conjugation is the Exercise 8.2 operation element `Measurement.opElement M (U.evolve
(ρ ⊗ σ)) m = Mₘ (U (ρ ⊗ σ) U†) Mₘ†`; `tr_E` is the partial trace over the right (environment)
factor. Its trace is the outcome probability (`bornProb_eq_trace_generalMeasurementEnvOp`) and
its normalization `Eₘ(ρ)/tr[Eₘ(ρ)]` is the final state of `Q` alone. (partial trace of a raw
operator).
-/
def generalMeasurementEnvOp (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) : Q →L[ℂ] Q :=
  (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ E.space)
    ((M.opElement (U.evolve (ρ ⊗ σ)) m).toLinearMap
      : Q.space ⊗[ℂ] E.space →ₗ[ℂ] Q.space ⊗[ℂ] E.space)).toContinuousLinearMap

/-- **Nielsen & Chuang, Exercise 8.7 (probabilities).** The probability of outcome `m` — the Born
probability of the general measurement `M` on the post-interaction joint state `U.evolve (ρ ⊗
σ)` — equals the trace of the induced operation:

`(p(m) : ℂ) = tr[Eₘ(ρ)]`.

Stated as the complex equality (which records both that `tr[Eₘ(ρ)]` is real and that it equals
the Born probability), for an arbitrary system, environment, state, environment state,
interaction, and outcome.
-/
theorem bornProb_eq_trace_generalMeasurementEnvOp (M : Measurement ι (Q ⊗ E))
    (U : Evolution (Q ⊗ E)) (σ : State E) (ρ : State Q) (m : ι) :
    (M.bornProb (U.evolve (ρ ⊗ σ)) m : ℂ)
      = LinearMap.trace ℂ Q.space (generalMeasurementEnvOp M U σ ρ m : Q.space →ₗ[ℂ] Q.space) :=
        sorry

/-- **The operation elements of Exercise 8.7's operator-sum representation.** Given an ensemble
decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|` of the environment state (the ensemble weights `√qⱼ` absorbed
into the vectors `wⱼ`, so `wⱼ = √qⱼ |j⟩` in N&C's notation) and the fixed environment
orthonormal basis `{eₖ}` (`stdOrthonormalBasis ℂ E.space`), the `(j, k)`-th operation element is

`Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩`,

Nielsen–Chuang's `Eⱼₖ = √qⱼ ⟨eₖ| Mₘ U |j⟩` of Eq. (8.35), generalized from the projectors `Pₘ`
to the general measurement operators `Mₘ`. (a raw operator built from the measurement/evolution
underlying operators).
-/
def generalMeasurementEnvKrausOp (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    {κ : Type*} (w : κ → E.space) (m : ι) (j : κ)
    (k : Fin (Module.finrank ℂ E.space)) : Q.space →ₗ[ℂ] Q.space :=
  LinearMap.krausOp (stdOrthonormalBasis ℂ E.space)
    (((M.op m).comp U.op).toLinearMap ∘ₗ LinearMap.tmulRightVec (w j)) k

/-- **Nielsen & Chuang, Exercise 8.7 (operator-sum representation).** Given an ensemble
decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|` of the environment state (hypothesis `hσ`; N&C's `σ = ∑ⱼ qⱼ
|j⟩⟨j|` with the weights absorbed, `wⱼ = √qⱼ |j⟩`), the induced operation `Eₘ` has the
operator-sum representation

`Eₘ(ρ) = ∑ⱼ ∑ₖ Eⱼₖ ρ Eⱼₖ†`,   `Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩`   (N&C Eqs. (8.33)–(8.35), `Pₘ ↦ Mₘ`),

the operation elements being `generalMeasurementEnvKrausOp`. Stated at the `Q.space →ₗ[ℂ]
Q.space` level (the coercion of the operation, applied to the density operator `ρ.op`).
-/
theorem generalMeasurementEnvOp_eq_sum_krausOp (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) {κ : Type*} [Fintype κ] (w : κ → E.space)
    (hσ : (σ.op : E.space →ₗ[ℂ] E.space)
      = ∑ j, ((InnerProductSpace.rankOne ℂ (w j) (w j)).toLinearMap : E.space →ₗ[ℂ] E.space)) :
    (generalMeasurementEnvOp M U σ ρ m : Q.space →ₗ[ℂ] Q.space)
      = ∑ j, ∑ k, generalMeasurementEnvKrausOp M U w m j k ∘ₗ (ρ.op : Q.space →ₗ[ℂ] Q.space)
          ∘ₗ LinearMap.adjoint (generalMeasurementEnvKrausOp M U w m j k) := sorry

end AxQM
