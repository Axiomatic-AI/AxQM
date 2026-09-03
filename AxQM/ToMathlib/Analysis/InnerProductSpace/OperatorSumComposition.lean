/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumCP

/-!
# Composition of operator-sum (Kraus) maps — Nielsen–Chuang Exercise 8.6

The **composition** of two quantum operations is again a quantum operation. Concretely, if `E`
has operator-sum (Kraus) representation `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` and `F` has representation
`F(σ) = Σⱼ Fⱼ σ Fⱼ†`, then the composite `(F ∘ E)(ρ) = Σⱼ Σᵢ Fⱼ Eᵢ ρ Eᵢ† Fⱼ†` is itself an
operator-sum map, with operation elements the products `{Fⱼ Eᵢ}`. This is Nielsen–Chuang
*Quantum Computation and Quantum Information*, **Exercise 8.6** (§8.2, p. 362).

## Main results

* `ContinuousLinearMap.IsOperatorSum.comp` — **Exercise 8.6:** if `Φ` and `Ψ` have operator-sum
  representations (`IsOperatorSum E Φ`, `IsOperatorSum F Ψ`) then the composite `Ψ ∘ Φ` has the
  operator-sum representation given by the product family `{Fⱼ Eᵢ}`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (Exercise 8.6).
-/

@[expose] public section

namespace ContinuousLinearMap

section

variable {H G K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The composite of two operator-sum (Kraus) maps is the operator-sum map of the product family**
(Nielsen–Chuang Exercise 8.6). For families `E : ι → (H →L[ℂ] G)` and `F : κ → (G →L[ℂ] K)`, the
composition of the operator-sum maps `krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` and `krausSumₗ F : σ ↦ Σⱼ Fⱼ σ
Fⱼ†` equals the single operator-sum map of the product family `(j, i) ↦ Fⱼ ∘ Eᵢ`:
`(krausSumₗ F) ∘ (krausSumₗ E) = krausSumₗ (fun p : κ × ι => Fₚ₁ ∘ Eₚ₂)`. -/
theorem krausSumₗ_comp (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K) :
    (krausSumₗ F).comp (krausSumₗ E)
      = krausSumₗ (fun p : κ × ι => (F p.1).comp (E p.2)) := by
  refine LinearMap.ext fun ρ => ?_
  rw [LinearMap.comp_apply, krausSumₗ_apply E, map_sum]
  rw [krausSumₗ_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [adjoint_comp, comp_assoc]

/-- **Factorization of the composite-family completeness sum** (Nielsen–Chuang Exercise 8.6). For
families `E : ι → (H →L[ℂ] G)` and `F : κ → (G →L[ℂ] K)`, the completeness sum of the product
family `(j, i) ↦ Fⱼ ∘ Eᵢ` reassociates as `Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) = Σᵢ Eᵢ† (Σⱼ Fⱼ† Fⱼ) Eᵢ`. -/
theorem sum_adjoint_comp_comp_eq_sum (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K) :
    ∑ p : κ × ι, adjoint ((F p.1).comp (E p.2)) ∘L (F p.1).comp (E p.2)
      = ∑ i, adjoint (E i) ∘L (∑ j, adjoint (F j) ∘L F j) ∘L E i := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finset_sum_comp, comp_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adjoint_comp]
  simp only [comp_assoc]

/-- **The product family inherits the operator-sum trace condition** (Nielsen–Chuang Exercise 8.6).
If `Σᵢ Eᵢ† Eᵢ ≤ 1` and `Σⱼ Fⱼ† Fⱼ ≤ 1`, then the product family `(j, i) ↦ Fⱼ ∘ Eᵢ` satisfies
`Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) ≤ 1`. This is the trace condition for the composite quantum operation. -/
theorem sum_adjoint_comp_comp_le_one (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K)
    (hE : ∑ i, adjoint (E i) ∘L E i ≤ 1) (hF : ∑ j, adjoint (F j) ∘L F j ≤ 1) :
    ∑ p : κ × ι, adjoint ((F p.1).comp (E p.2)) ∘L (F p.1).comp (E p.2) ≤ 1 := by
  rw [sum_adjoint_comp_comp_eq_sum]
  set B := ∑ j, adjoint (F j) ∘L F j
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) hE
  -- `Eᵢ† B Eᵢ ≤ Eᵢ† Eᵢ`, since `B ≤ 1` and conjugation is Loewner-monotone.
  have hp := (nonneg_iff_isPositive _).mp (sub_nonneg.mpr hF)
  have hcj := hp.conj_adjoint (adjoint (E i))
  rw [adjoint_adjoint] at hcj
  have h2 := (nonneg_iff_isPositive _).mpr hcj
  have hexp : adjoint (E i) ∘L (1 - B) ∘L E i
      = adjoint (E i) ∘L E i - adjoint (E i) ∘L B ∘L E i := by
    rw [sub_comp, comp_sub, one_def, id_comp]
  rw [hexp] at h2
  exact sub_nonneg.mp h2

/-- **The product family inherits operator-sum trace-preservation** (Nielsen–Chuang Exercise 8.6).
If `Σᵢ Eᵢ† Eᵢ = 1` and `Σⱼ Fⱼ† Fⱼ = 1`, then the product family `(j, i) ↦ Fⱼ ∘ Eᵢ` is
trace-preserving:
`Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) = 1`: the trace-preservation of the composite `Ψ ∘ Φ` of two
trace-preserving operations. -/
theorem sum_adjoint_comp_comp_eq_one (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K)
    (hE : ∑ i, adjoint (E i) ∘L E i = 1) (hF : ∑ j, adjoint (F j) ∘L F j = 1) :
    ∑ p : κ × ι, adjoint ((F p.1).comp (E p.2)) ∘L (F p.1).comp (E p.2) = 1 := by
  rw [sum_adjoint_comp_comp_eq_sum, hF]
  simp only [one_def, id_comp]
  exact hE

/-- **The composition of quantum operations is a quantum operation** (Nielsen–Chuang, *Quantum
Computation and Quantum Information*, **Exercise 8.6**). If superoperators `Φ` and `Ψ` have
operator-sum (Kraus) representations — `IsOperatorSum E Φ` (i.e. `Φ = krausSumₗ E` with
`Σᵢ Eᵢ† Eᵢ ≤ 1`) and `IsOperatorSum F Ψ` — then their composite `Ψ ∘ Φ` has the operator-sum
representation given by the product family `(j, i) ↦ Fⱼ ∘ Eᵢ`,
`IsOperatorSum (fun p ↦ Fₚ₁ ∘ Eₚ₂) (Ψ ∘ Φ)`. The spaces need not coincide
(`E : ι → H →L[ℂ] G`, `F : κ → G →L[ℂ] K`). -/
theorem IsOperatorSum.comp {E : ι → H →L[ℂ] G} {F : κ → G →L[ℂ] K}
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] G →L[ℂ] G} {Ψ : (G →L[ℂ] G) →ₗ[ℂ] K →L[ℂ] K}
    (hE : IsOperatorSum E Φ) (hF : IsOperatorSum F Ψ) :
    IsOperatorSum (fun p : κ × ι => (F p.1).comp (E p.2)) (Ψ.comp Φ) := by
  obtain ⟨hΦ, hEcond⟩ := hE
  obtain ⟨hΨ, hFcond⟩ := hF
  refine ⟨?_, sum_adjoint_comp_comp_le_one E F hEcond hFcond⟩
  rw [hΦ, hΨ, krausSumₗ_comp]

end

section

end

end ContinuousLinearMap
