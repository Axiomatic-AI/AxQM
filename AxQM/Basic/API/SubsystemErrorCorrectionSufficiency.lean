/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SubsystemErrorCorrectionMarginal
import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# AxQM.Basic.API — decoupling is sufficient to correct errors on a subsystem

**Nielsen & Chuang, Exercise 12.14** (p. 567), the *sufficiency* direction.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

variable {Q₁ Q₂ : QSystem} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **N&C Exercise 12.14 — decoupling is sufficient to correct errors on `Q₁`** (recovery
operator-sum form). Under the decoupling condition `ρ^{RQ1} = ρ^R ⊗ ρ₁`, there is a
**trace-preserving recovery** family `R` (`∑ₒ Rₒ† Rₒ = 1`) that **corrects** the complete
`Q₁`-error family `leftFactorErrorBasis b` on the code (`ContinuousLinearMap.Corrects`): the
composed noise-then-recovery returns every operator supported on the code to a scalar multiple
of itself. -/
theorem exists_correction_of_decoupledLeftFactor {R : Type*} [NormedAddCommGroup R]
    [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] (e : OrthonormalBasis ι ℂ R)
    {ιb : Type} [Fintype ιb] (b : OrthonormalBasis ιb ℂ Q₁.space) {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] (bB : OrthonormalBasis κ ℂ Q₂.space)
    (bAB : OrthonormalBasis κ' ℂ (Q₁.space ⊗[ℂ] Q₂.space)) {w : ι → (Q₁ ⊗ Q₂).space}
    (hw : Orthonormal ℂ w) (ρ1 : Q₁.space →ₗ[ℂ] Q₁.space)
    (hdec : (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R Q₁.space Q₂.space).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1) :
    ∃ (γ : Type) (_ : Fintype γ) (Rec : γ → (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space),
      (∑ o, ContinuousLinearMap.adjoint (Rec o) ∘L Rec o = 1) ∧
        ContinuousLinearMap.Corrects (∑ i, rankOne ℂ (w i) (w i))
          (leftFactorErrorBasis (Q₂ := Q₂) b) Rec := sorry

/-- **N&C Exercise 12.14 — decoupling yields a recovery channel correcting the `Q₁`-errors**
(channel form). -/
theorem exists_correctionChannel_of_decoupledLeftFactor {R : Type*} [NormedAddCommGroup R]
    [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] (e : OrthonormalBasis ι ℂ R)
    {ιb : Type} [Fintype ιb] (b : OrthonormalBasis ιb ℂ Q₁.space) {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] (bB : OrthonormalBasis κ ℂ Q₂.space)
    (bAB : OrthonormalBasis κ' ℂ (Q₁.space ⊗[ℂ] Q₂.space)) {w : ι → (Q₁ ⊗ Q₂).space}
    (hw : Orthonormal ℂ w) (ρ1 : Q₁.space →ₗ[ℂ] Q₁.space)
    (hdec : (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R Q₁.space Q₂.space).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1) :
    ∃ (γ : Type) (_ : Fintype γ) (Rec : γ → (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space)
      (rec : State (Q₁ ⊗ Q₂) → State (Q₁ ⊗ Q₂)),
      IsChannel rec ∧
        (∀ ρ : State (Q₁ ⊗ Q₂), (rec ρ).op = ContinuousLinearMap.krausSumₗ Rec ρ.op) ∧
          ∃ lam : ℝ, 0 ≤ lam ∧ ∀ ρ : State (Q₁ ⊗ Q₂),
            (∑ i, rankOne ℂ (w i) (w i)) ∘L ρ.op ∘L (∑ i, rankOne ℂ (w i) (w i)) = ρ.op →
              ContinuousLinearMap.krausSumₗ Rec
                  (ContinuousLinearMap.krausSumₗ (leftFactorErrorBasis (Q₂ := Q₂) b) ρ.op)
                = (lam : ℂ) • ρ.op := sorry

end AxQM
