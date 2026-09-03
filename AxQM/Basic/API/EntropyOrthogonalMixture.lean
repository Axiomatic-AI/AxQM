/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Support

/-!
# AxQM — entropy of a mixture with orthogonal supports (N&C Thm 11.8 part 4 / Thm 11.10)

For a mixture `μ = State.mix p ρ = ∑ᵢ pᵢ ρᵢ` of quantum states whose components have **orthogonal
supports**, the von Neumann entropy is *exactly* the average component entropy plus the Shannon
entropy of the weights.

## Main results

* `AxQM.State.vonNeumannEntropy_mix_orthogonalSupport` — Nielsen–Chuang Theorem 11.8
  part (4), `S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)` under `Pairwise ((ρ i).support ⟂ (ρ j).support)`.
-/

namespace AxQM

open scoped InnerProductSpace

variable {S : QSystem}

/-- **Entropy of an orthogonal-support mixture** (Nielsen–Chuang Theorem 11.8, part (4),
eq. (11.57)). For a probability distribution `p` and a family `ρ : ι → State S` whose supports are
**pairwise orthogonal** (`(ρ i).support ⟂ (ρ j).support` for `i ≠ j`), the von Neumann entropy of
the mixture `State.mix p hp hsum ρ = ∑ᵢ pᵢ ρᵢ` is the Shannon entropy `H(p)` of the weights plus the
`p`-average of the component entropies:

`S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.
-/
theorem State.vonNeumannEntropy_mix_orthogonalSupport {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (horth : Pairwise fun i j => (ρ i).support ⟂ (ρ j).support) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := sorry

end AxQM
