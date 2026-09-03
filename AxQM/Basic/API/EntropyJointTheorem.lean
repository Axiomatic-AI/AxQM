/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyOrthogonalMixture
import AxQM.Basic.API.EntropyComposite
import Mathlib.Analysis.InnerProductSpace.StarOrder
import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# AxQM — the joint entropy theorem (N&C Thm 11.8, part 5 / eq. (11.58))

The **joint entropy theorem** (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.8, part (5), eq. (11.58)).

## Main results

* `AxQM.State.vonNeumannEntropy_jointEntropyTheorem` — Nielsen–Chuang Theorem 11.8
  part (5), the joint entropy theorem `S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {A B : QSystem}

/-- **The joint entropy theorem** (Nielsen–Chuang Theorem 11.8, part (5), eq. (11.58)). For a
probability distribution `p`, an **orthonormal family of pure states** `|i⟩ = e i` of a system
`A` (`Orthonormal ℂ (fun i => (e i).vec)`), and an *arbitrary* family of states `ρ : ι → State
B`, the von Neumann entropy of the block-diagonal composite `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ` is the Shannon
entropy of the weights plus the `p`-average of the component entropies:

`S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.
-/
theorem State.vonNeumannEntropy_jointEntropyTheorem {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (e : ι → PureState A) (he : Orthonormal ℂ fun i => (e i).vec) (ρ : ι → State B) :
    (State.mix p hp hsum fun i => (e i).toState.tmul (ρ i)).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := sorry

end AxQM
