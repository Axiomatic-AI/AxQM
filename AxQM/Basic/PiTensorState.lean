/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.PiTensor
import AxQM.Basic.StateSpace
import AxQM.Basic.SystemIso
import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProductDensity

/-!
# AxQM.Basic — indexed product states (`⨂ₚ i, ψ i`)

Given a finite family of *pure* states `ψ : ∀ i, PureState (S i)`, their **indexed product state**
`⨂ₚ i, ψ i` is the pure state of `⨂ₛ i, S i` whose underlying vector is the n-ary elementary tensor
`⨂ₜ[ℂ] i, (ψ i).vec`.

## Main definitions

* `PureState.piTensor` (`⨂ₚ i, ψ i`) — the indexed product pure state of a finite family
  `ψ : ∀ i, PureState (S i)`, on `⨂ₛ i, S i`.
* `State.piTensor` (`⨂ₚ i, ρ i`) — the indexed product (mixed) state of a finite family
  `ρ : ∀ i, State (S i)`, on `⨂ₛ i, S i`.
* `QSystem.piTensorReindex` — the reindexing system isomorphism
  `⨂ₛ i, S i ≃ₛ ⨂ₛ j, S (e.symm j)` along `e : ι ≃ κ`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {S : ι → QSystem}

/-- **Indexed product pure state** `⨂ₚ i, ψ i`: the product of a finite family of pure states `ψ : ∀
i, PureState (S i)`, on the indexed composite `⨂ₛ i, S i`. -/
def PureState.piTensor (ψ : ∀ i, PureState (S i)) : PureState (⨂ₛ i, S i) where
  vec := ⨂ₜ[ℂ] i, (ψ i).vec
  normalized := by
    have h : (inner ℂ (⨂ₜ[ℂ] i, (ψ i).vec) (⨂ₜ[ℂ] i, (ψ i).vec) : ℂ) = 1 := by
      rw [PiTensorProduct.inner_tprod_tprod]
      exact Finset.prod_eq_one fun i _ ↦ by
        rw [inner_self_eq_norm_sq_to_K, (ψ i).normalized]; norm_num
    have h2 : ‖(⨂ₜ[ℂ] i, (ψ i).vec)‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]; simp
    calc ‖(⨂ₜ[ℂ] i, (ψ i).vec)‖
        = Real.sqrt (‖(⨂ₜ[ℂ] i, (ψ i).vec)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [h2, Real.sqrt_one]

@[inherit_doc PureState.piTensor]
scoped notation3:100 "⨂ₚ "(...)", "r:67:(scoped f => PureState.piTensor f) => r

/-- **Indexed product (mixed) state** `⨂ₚ i, ρ i`: the product of a finite family of states `ρ : ∀
i, State (S i)`, on the indexed composite `⨂ₛ i, S i`. -/
def State.piTensor (ρ : ∀ i, State (S i)) : State (⨂ₛ i, S i) where
  op := PiTensorProduct.mapCLM fun i ↦ (ρ i).op
  isDensity := PiTensorProduct.mapCLM_isDensityOp fun i ↦ (ρ i).isDensity

@[inherit_doc State.piTensor]
scoped notation3:100 "⨂ₚ "(...)", "r:67:(scoped f => State.piTensor f) => r

/-- **Reindexing an indexed composite** along an index equivalence `e : ι ≃ κ`: the system
isomorphism `⨂ₛ i, S i ≃ₛ ⨂ₛ j, S (e.symm j)`. -/
def QSystem.piTensorReindex (e : ι ≃ κ) (S : ι → QSystem) :
    (⨂ₛ i, S i) ≃ₛ ⨂ₛ j, S (e.symm j) :=
  ⟨PiTensorProduct.reindexₗᵢ ℂ (fun i ↦ (S i).space) e⟩

end AxQM
