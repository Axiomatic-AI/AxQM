/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.Basic.API.EntropyMixtureReverse
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.BellReducedState
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance
import AxQM.NC.Ch12.Problem12_1

/-!
# N&C Problem 12.2 — no-cloning from the monotonicity of the Holevo χ quantity

*(N&C p. 602.)*

Prove no-cloning by showing cloning non-orthogonal pure states increases chi.

* `unif2`
* `unif2_nonneg`
* `unif2_sum`
* `holevoChi_lt_holevoChi_clone`
* `no_cloning`
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The uniform two-point distribution `(½, ½)`. -/
private def unif2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

private theorem unif2_nonneg : ∀ i, 0 ≤ unif2 i := by intro i; fin_cases i <;> norm_num [unif2]

private theorem unif2_sum : ∑ i, unif2 i = 1 := by norm_num [unif2, Fin.sum_univ_two]

/-- **Cloning strictly increases the Holevo χ quantity** (the heart of Nielsen & Chuang Problem
12.2). For two non-orthogonal, distinct pure states — `0 < F(|ψ₁⟩, |ψ₂⟩)` and `F(|ψ₁⟩, |ψ₂⟩) <
1`, i.e. overlap `0 < c < 1` — the Holevo χ of the *cloned* equiprobable ensemble `{½, |ψ₁⟩|ψ₁⟩;
½, |ψ₂⟩|ψ₂⟩}` strictly exceeds that of `{½, |ψ₁⟩; ½, |ψ₂⟩}`:

`χ({½, |ψᵢ⟩}) < χ({½, |ψᵢ⟩|ψᵢ⟩})`. -/
theorem holevoChi_lt_holevoChi_clone (ψ₁ ψ₂ : PureState S)
    (h0 : 0 < ψ₁.toState.fidelity ψ₂.toState) (h1 : ψ₁.toState.fidelity ψ₂.toState < 1) :
    State.holevoChi unif2 unif2_nonneg unif2_sum (fun i => (![ψ₁, ψ₂] i).toState)
      < State.holevoChi unif2 unif2_nonneg unif2_sum
          (fun i => (![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂] i).toState) := sorry

/-- **The no-cloning theorem** (Nielsen & Chuang Problem 12.2), via the monotonicity of the Holevo χ
quantity under quantum operations. There is **no** cloning process for two non-orthogonal,
distinct pure states `|ψ₁⟩`, `|ψ₂⟩` (`0 < F(|ψ₁⟩, |ψ₂⟩) < 1`).

A cloning process is presented as a quantum operation on `S ⊗ S` by its Chapter-8 dilation (N&C
Problem 12.1(2), `State.dilatedChannel`): adjoin a blank target `|blank⟩` and an environment
`|ω⟩`, evolve by a unitary `U` on `(S ⊗ S) ⊗ C`, and discard the environment. Cloning means
`E(|ψᵢ⟩ ⊗ |blank⟩) = |ψᵢ⟩ ⊗ |ψᵢ⟩`.
-/
theorem no_cloning {C : QSystem} (ψ₁ ψ₂ blank : PureState S) (U : Evolution ((S ⊗ S) ⊗ C))
    (ω : PureState C)
    (hclone₁ : State.dilatedChannel (ψ₁.toState.tmul blank.toState) U ω = (ψ₁.tmul ψ₁).toState)
    (hclone₂ : State.dilatedChannel (ψ₂.toState.tmul blank.toState) U ω = (ψ₂.tmul ψ₂).toState)
    (h0 : 0 < ψ₁.toState.fidelity ψ₂.toState)
    (h1 : ψ₁.toState.fidelity ψ₂.toState < 1) : False := sorry

end AxQM
