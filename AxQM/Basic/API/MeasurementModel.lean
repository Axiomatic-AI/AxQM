/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.ProjectiveMeasurement
import AxQM.Basic.API.GeneralMeasurementEnvironment
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation
import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# AxQM — the measurement model of a set of quantum operations (N&C Exercise 8.9)

The physics building the **measurement model** of Nielsen–Chuang Exercise 8.9.
Given a set of quantum operations `{Eₘ}` whose sum `∑ₘ Eₘ` is trace preserving, presented flatly by
a family of operation elements `E : ι → (Q →L Q)` (the `E_{mk}` of the exercise) together with a
labelling `out : ι → M` recording which outcome each element belongs to (`out (m,k) = m`), and an
environment `Env` with an orthonormal basis `b : OrthonormalBasis ι ℂ Env` in one-to-one
correspondence with the operation-element indices and a standard unit state `e₀`, this file
constructs the two physical objects the exercise measures.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (System–environment models; Box 8.1; Exercise 8.9).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι M : Type*} [Fintype ι] [Fintype M] [DecidableEq M] {S : QSystem}

/-- **The block-projective measurement grouped by a labelling** `out : ι → M` of an orthonormal
basis `b` of `S` (Nielsen–Chuang Exercise 8.9's environment measurement `Pₘ ≡ ∑ₖ |m,k⟩⟨m,k|`).
-/
def Measurement.ofOrthonormalBasisFiber (b : OrthonormalBasis ι ℂ S) (out : ι → M) :
    Measurement M S where
  op m := orthonormalProjector ℂ (⇑b) (Finset.univ.filter (fun σ => out σ = m))
  complete := by
    set P : Finset ι → (S →L[ℂ] S) := orthonormalProjector ℂ (⇑b) with hP
    have hsq : ∀ s : Finset ι, (adjoint (P s)).comp (P s) = P s := by
      intro s
      have hsp : IsStarProjection (P s) :=
        hP ▸ isStarProjection_orthonormalProjector b.orthonormal s
      rw [← ContinuousLinearMap.star_eq_adjoint, hsp.isSelfAdjoint.star_eq,
        ← ContinuousLinearMap.mul_def]
      exact hsp.isIdempotentElem
    calc ∑ m, (adjoint (P (Finset.univ.filter (fun σ => out σ = m)))).comp
            (P (Finset.univ.filter (fun σ => out σ = m)))
        = ∑ m, P (Finset.univ.filter (fun σ => out σ = m)) :=
          Finset.sum_congr rfl fun m _ => hsq _
      _ = ∑ σ, rankOne ℂ (b σ) (b σ) := by
          rw [hP]; exact Finset.sum_fiberwise Finset.univ out (fun σ => rankOne ℂ (b σ) (b σ))
      _ = 1 := by rw [b.sum_rankOne_eq_id, ← ContinuousLinearMap.one_def]

variable {Q Env : QSystem}

/-- **The joint unitary of the measurement model** (Nielsen–Chuang Exercise 8.9, eq. (8.40)). From a
family of operation elements `E : ι → (Q →L Q)` for a trace-preserving `∑ₘ Eₘ` (`hE : ∑_σ (E σ)†
(E σ) = 1`), an orthonormal environment basis `b` in one-to-one correspondence with the indices,
and a standard unit environment state `e₀`, the joint dynamics is the unitary `U` acting as
`U (ψ ⊗ e₀) = ∑_σ (E σ ψ) ⊗ (b σ)`, packaged as an `Evolution (Q ⊗ Env)`. -/
def measurementModelEvolution (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space} (he₀ : ‖e₀‖ = 1)
    (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1) :
    Evolution (Q ⊗ Env) :=
  Evolution.ofLinearIsometryEquiv
    (LinearMap.exists_unitary_krausDilation b (fun σ => (E σ).toLinearMap)
      (ContinuousLinearMap.sum_adjoint_comp_toLinearMap_eq_id E hE) he₀).choose

/-- **The joint unitary on the standard-ancilla slice** (Nielsen–Chuang Exercise 8.9, eq. (8.40)):
`U (ψ ⊗ e₀) = ∑_σ (E σ ψ) ⊗ (b σ)`. -/
theorem measurementModelEvolution_op_tmul (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space}
    (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1) (ψ : Q) :
    (measurementModelEvolution b he₀ E hE).op (ψ ⊗ₜ[ℂ] e₀) = ∑ σ, E σ ψ ⊗ₜ[ℂ] b σ := sorry

/-- **The `m`-th induced operation element of the measurement model** (Nielsen–Chuang Exercise 8.9):
`Eₘ(ρ) = ∑_{out σ = m} E_σ ρ E_σ†`, the quantum operation `Eₘ` of the labelled Kraus family applied
to the principal state `ρ`, collecting exactly the operation elements `E_σ` whose outcome label is
`m` (N&C's `Eₘ(ρ) = ∑ₖ E_{mk} ρ E_{mk}†`). -/
def measurementModelInducedOp (E : ι → (Q →L[ℂ] Q)) (out : ι → M) (ρ : State Q) (m : M) :
    Q →L[ℂ] Q :=
  ∑ σ ∈ Finset.univ.filter (fun σ => out σ = m), (E σ).comp (ρ.op.comp (adjoint (E σ)))

/-- **Nielsen & Chuang, Exercise 8.9 (outcome probability).** Performing `U` on `ρ ⊗ |e₀⟩⟨e₀|` and
then measuring the environment block projector `Pₘ` gives outcome `m` with probability the trace
of the induced operation element, `p(m) = tr(Eₘ ρ)`. Stated as the complex equality `(p(m) : ℂ)
= tr(Eₘ ρ)`, which records both that the trace is real and that it equals the Born probability. -/
theorem measurementModel_bornProb_eq_trace (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space}
    (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1)
    (out : ι → M) (ρ : State Q) (m : M) :
    (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).bornProb
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m : ℂ)
      = LinearMap.trace ℂ Q.space
          (measurementModelInducedOp E out ρ m : Q.space →ₗ[ℂ] Q.space) := sorry

/-- **Nielsen & Chuang, Exercise 8.9 (post-measurement state).** The corresponding post-measurement
state of the *principal* system — the left marginal (`State.reducedLeft`, tracing out the
environment) of the normalized post-measurement joint state `M.postMeasurement …` — is the
induced operation element normalized by its trace, `Eₘ(ρ)/tr(Eₘ ρ)` (N&C's `Eₘ(ρ)/tr(Eₘ(ρ))`),
whenever the outcome is possible (`hp : p(m) ≠ 0`). -/
theorem measurementModel_reducedLeft_postMeasurement_op (b : OrthonormalBasis ι ℂ Env)
    {e₀ : Env.space} (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q))
    (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1) (out : ι → M) (ρ : State Q) (m : M)
    (hp : ((Measurement.ofOrthonormalBasisFiber b out).onRight Q).bornProb
      ((measurementModelEvolution b he₀ E hE).evolve
        (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m ≠ 0) :
    (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).postMeasurement
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m hp).reducedLeft.op
      = (LinearMap.trace ℂ Q.space (measurementModelInducedOp E out ρ m : Q.space →ₗ[ℂ] Q.space))⁻¹
          • measurementModelInducedOp E out ρ m := sorry

end AxQM
