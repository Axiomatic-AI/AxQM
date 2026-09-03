/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.Basic.API.Purity
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.ToMathlib.Analysis.InnerProductSpace.Matricization
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# AxQM — the Schmidt number of a bipartite pure state (generator + bridges)

The **Schmidt number** of a pure state `ψ` of a composite system `S ⊗ T`
(Nielsen–Chuang §2.5): the number of non-zero *Schmidt coefficients* in the
Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`. The Schmidt
coefficients are exactly the singular values of the *coefficient operator*
`M = matricize ψ.vec : T.space →L S.space` — the linear map whose matrix in fixed
orthonormal bases is the coefficient array `a` with `ψ = ∑ⱼₖ aⱼₖ |j⟩|k⟩` — so the
Schmidt number is the number of non-zero singular values of `M`.

## Main definitions

* `AxQM.PureState.schmidtNumber` — the Schmidt number of a bipartite pure
  state (number of non-zero singular values of the matricized coefficient operator).
* `AxQM.State.rank` — the rank of a (density-operator) state: the dimension
  of the range of its operator.

## Main results (bridges)

* `PureState.schmidtNumber_le_card_of_sum_tmul` — **Problem 2.2(2)**: if `|ψ⟩ = ∑ⱼ |αⱼ⟩|βⱼ⟩`
  is a product decomposition into `s.card` (un-normalized) terms, then `Sch(ψ) ≤ s.card`.
* `PureState.natAbs_sub_schmidtNumber_le` — **Problem 2.2(3)**: if `|ψ⟩ = α|φ⟩ + β|γ⟩` with
  `α, β ≠ 0`, then `Sch(ψ) ≥ |Sch(φ) − Sch(γ)|` (a reverse-triangle bound). The nonzero
  amplitudes are a genuine correctness hypothesis, not a weakening: with `α = 0` the state is
  `|ψ⟩ = β|γ⟩` and the inequality fails (take `|φ⟩` maximally entangled, `|γ⟩` a product state).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **coefficient operator** of a bipartite pure state, matricized against the standard
orthonormal basis of the *right* factor `T`. Shared; shared by the Schmidt-number bridges below
and by the subadditivity/triangle results (Problem 2.2(2),(3)). -/
def PureState.schmidtOp (ψ : PureState (S ⊗ T)) : T.space →L[ℂ] S.space :=
  TensorProduct.matricize (stdOrthonormalBasis ℂ T.space) (ψ.vec : S.space ⊗[ℂ] T.space)

/-- **Schmidt number** of a bipartite pure state (Nielsen–Chuang §2.5): the number of
non-zero Schmidt coefficients `λᵢ` in the Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`.
The Schmidt coefficients are the singular values of the matricized coefficient operator
`M = matricize ψ.vec`, so this counts its non-zero singular values. -/
def PureState.schmidtNumber (ψ : PureState (S ⊗ T)) : ℕ :=
  ψ.schmidtOp.toLinearMap.singularValues.support.card

/-- **Rank of a state**: the dimension of the range of its density operator. -/
def State.rank (ρ : State S) : ℕ :=
  Module.finrank ℂ (LinearMap.range (ρ.op : S.space →ₗ[ℂ] S.space))

/-- **Problem 2.2(2).** If a bipartite pure state `|ψ⟩` has a product decomposition
`|ψ⟩ = ∑ⱼ |αⱼ⟩|βⱼ⟩` into `s.card` (possibly un-normalized) terms, then its Schmidt number is
at most the number of terms, `Sch(ψ) ≤ s.card`.
-/
theorem PureState.schmidtNumber_le_card_of_sum_tmul {ι : Type*} (s : Finset ι)
    (ψ : PureState (S ⊗ T)) (a : ι → S.space) (b : ι → T.space)
    (h : (ψ.vec : S.space ⊗[ℂ] T.space) = ∑ j ∈ s, a j ⊗ₜ[ℂ] b j) :
    ψ.schmidtNumber ≤ s.card := sorry

/-- **Problem 2.2(3).** If a bipartite pure state `|ψ⟩` is a superposition `|ψ⟩ = α|φ⟩ + β|γ⟩`
of two pure states with *nonzero* amplitudes `α, β`, then its Schmidt number satisfies the
reverse-triangle bound `Sch(ψ) ≥ |Sch(φ) − Sch(γ)|`.

The nonzero amplitudes are a genuine correctness hypothesis, not a weakening of N&C: with
`α = 0` the state is `|ψ⟩ = β|γ⟩`, physically `|γ⟩`, so `Sch(ψ) = Sch(γ)`; taking `|φ⟩`
maximally entangled and `|γ⟩` a product state then makes `|Sch(φ) − Sch(γ)|` exceed `Sch(ψ)`
and the inequality genuinely fails. N&C's statement tacitly assumes a two-term superposition,
so `α, β ≠ 0` is the faithful reading. -/
theorem PureState.natAbs_sub_schmidtNumber_le (α β : ℂ) (φ γ ψ : PureState (S ⊗ T))
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hψ : (ψ.vec : S.space ⊗[ℂ] T.space)
        = α • (φ.vec : S.space ⊗[ℂ] T.space) + β • (γ.vec : S.space ⊗[ℂ] T.space)) :
    ((φ.schmidtNumber : ℤ) - γ.schmidtNumber).natAbs ≤ ψ.schmidtNumber := sorry

end AxQM
