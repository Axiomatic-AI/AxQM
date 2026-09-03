/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation

/-!
# System–environment models for non-trace-preserving operations (N&C Exercise 8.8)

## Main definitions and results

* `ContinuousLinearMap.krausComplement E` — the extra operation element
  `E∞ = √(1 − Σₖ Eₖ† Eₖ)`, the CFC square root of the defect.
* `ContinuousLinearMap.krausAugment E` — the augmented family `Option ι → H →L H`
  (`some k ↦ Eₖ`, `none ↦ E∞`).
* `ContinuousLinearMap.sum_adjoint_krausAugment_comp_self` — **the exercise's answer:** the
  augmented family is complete, `Σⱼ Fⱼ† Fⱼ = 1` (`Σₖ Eₖ† Eₖ = 1` including `k = ∞`).
* `LinearMap.krausComplementProj b` — the environment post-selection projector
  `P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)` (N&C's projector `P` of Eq. (8.36), with `e∞ = b none`).
* `LinearMap.exists_unitary_proj_krausComplement` — **the model:** for any non-trace-preserving
  family (`Σₖ Eₖ† Eₖ ≤ 1`) and unit environment state `ω`, there is a **unitary** `U` on the joint
  space with `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = Σₖ Eₖ ρ Eₖ†` for all `ρ`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (System–environment models; Box 8.1; Exercise 8.8).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] {ι : Type*} [Fintype ι]

/-- **The extra operation element `E∞` of Nielsen–Chuang Exercise 8.8.** For a family
`E : ι → H →L H` of operation elements of a *non-trace-preserving* operation
(`Σₖ Eₖ† Eₖ ≤ 1`), the defect `1 − Σₖ Eₖ† Eₖ` is a positive operator; `krausComplement E` is
its operator square root `E∞ = √(1 − Σₖ Eₖ† Eₖ)`, via the continuous functional calculus. -/
noncomputable def krausComplement (E : ι → H →L[ℂ] H) : H →L[ℂ] H :=
  cfc Real.sqrt (1 - ∑ k, adjoint (E k) ∘L E k)

/-- **The augmented family** of Nielsen–Chuang Exercise 8.8: the family `E`, extended by the
extra element `E∞ = krausComplement E` at `none`. -/
noncomputable def krausAugment (E : ι → H →L[ℂ] H) : Option ι → H →L[ℂ] H :=
  fun j => j.elim (krausComplement E) E

omit [FiniteDimensional ℂ H] in
/-- **The augmented family is complete — the answer to Nielsen–Chuang Exercise 8.8.** Adjoining the
extra element `E∞ = krausComplement E` to a non-trace-preserving family `{Eₖ}` (`Σₖ Eₖ† Eₖ ≤ 1`)
yields the completeness relation

`Σⱼ Fⱼ† Fⱼ = 1`   (over `j : Option ι`),

i.e. N&C's `Σₖ Eₖ† Eₖ = 1` where the sum ranges over the complete set of `k` *including*
`k = ∞`.
-/
theorem sum_adjoint_krausAugment_comp_self (E : ι → H →L[ℂ] H)
    (hE : ∑ k, adjoint (E k) ∘L E k ≤ 1) :
    ∑ j : Option ι, adjoint (krausAugment E j) ∘L krausAugment E j = 1 := sorry

end ContinuousLinearMap

namespace LinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace F]

omit [FiniteDimensional ℂ H] [CompleteSpace H] [FiniteDimensional ℂ F] [CompleteSpace F] in
/-- **The environment post-selection projector of Nielsen–Chuang Eq. (8.36)** for Exercise 8.8:
`P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)`, the orthogonal projector onto the subspace where the environment is
*not* in the extra state `e∞ = b none`. -/
noncomputable def krausComplementProj (b : OrthonormalBasis (Option ι) ℂ F) :
    (H ⊗[ℂ] F) →ₗ[ℂ] (H ⊗[ℂ] F) :=
  TensorProduct.map LinearMap.id
    ((LinearMap.id : F →ₗ[ℂ] F) - (InnerProductSpace.rankOne ℂ (b none) (b none)).toLinearMap)

/-- **A unitary system–environment model for a non-trace-preserving operation** (Nielsen–Chuang
Exercise 8.8, Eq. (8.36)).

`tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = Σₖ Eₖ ρ Eₖ†`   for all `ρ`.

This is the construction the exercise asks for.
-/
theorem exists_unitary_proj_krausComplement (b : OrthonormalBasis (Option ι) ℂ F)
    (E : ι → H →L[ℂ] H) (hE : ∑ k, ContinuousLinearMap.adjoint (E k) ∘L E k ≤ 1)
    {ω : F} (hω : ‖ω‖ = 1) :
    ∃ U : (H ⊗[ℂ] F) ≃ₗᵢ[ℂ] (H ⊗[ℂ] F),
      ∀ ρ : H →ₗ[ℂ] H,
        partialTraceRight b (krausComplementProj b ∘ₗ
            (U.toLinearMap ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne ℂ ω ω).toLinearMap
              ∘ₗ adjoint U.toLinearMap)
            ∘ₗ krausComplementProj b)
          = ∑ k, (E k : H →ₗ[ℂ] H) ∘ₗ ρ ∘ₗ LinearMap.adjoint ((E k : H →ₗ[ℂ] H)) := sorry

end LinearMap
