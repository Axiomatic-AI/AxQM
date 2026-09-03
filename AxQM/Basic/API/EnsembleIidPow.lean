/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TensorPowState
import AxQM.Basic.API.Ensemble

/-!
# AxQM.Basic.API — the i.i.d. product ensemble `{p_J, |ψ_J⟩}` and `ρ^⊗n`

For an **ensemble of pure states** `e = {pⱼ, |ψⱼ⟩}` (Nielsen & Chuang §2.4.1) with density
operator `ρ = e.toState = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|`, its **`n`-fold i.i.d. product ensemble** models `n`
independent uses of the source: it emits the product state `|ψ_J⟩ = |ψ_{j₁}⟩ ⊗ ⋯ ⊗ |ψ_{jₙ}⟩` with
probability `p_J = p_{j₁} ⋯ p_{jₙ}`, over all index sequences `J = (j₁, …, jₙ)`. This is the source
model of Nielsen & Chuang Exercise 12.8 (compression of an ensemble of quantum states, eq. (12.61)).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2, Exercise 12.8, eq. (12.61).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : ι → QSystem}

variable {T : QSystem}

/-- **The `n`-fold i.i.d. product ensemble** of an ensemble `e = {pⱼ, |ψⱼ⟩}` (Nielsen & Chuang
Exercise 12.8). It emits the product pure state `|ψ_J⟩ = ⨂ᵢ |ψ_{Jᵢ}⟩` with probability `p_J = ∏ᵢ
p_{Jᵢ}`. -/
def Ensemble.iidPow (e : Ensemble T) (n : ℕ) : Ensemble (T ^⊗ₛ n) where
  card := e.card ^ n
  prob j := ∏ i, e.prob (finFunctionFinEquiv.symm j i)
  states j := ⨂ₚ i, e.states (finFunctionFinEquiv.symm j i)
  prob_nonneg j := Finset.prod_nonneg fun i _ => e.prob_nonneg _
  sum_prob := by
    rw [Equiv.sum_comp finFunctionFinEquiv.symm (fun J => ∏ i, e.prob (J i)),
      ← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
      Finset.prod_congr rfl (fun i _ => e.sum_prob), Finset.prod_const_one]

end AxQM
