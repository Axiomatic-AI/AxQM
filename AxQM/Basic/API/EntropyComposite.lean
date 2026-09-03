/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.MaximallyMixed
import AxQM.Basic.Composite

/-!
# AxQM — von Neumann entropy of a product state

The von Neumann entropy `State.vonNeumannEntropy` of an uncorrelated composite.

## Main results

* `AxQM.State.vonNeumannEntropy_tmul` — `S(ρ ⊗ σ) = S(ρ) + S(σ)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Additivity of the von Neumann entropy over a product state** (Nielsen & Chuang, Exercise
11.13): for states `ρ : State S` and `σ : State T`, the entropy of the uncorrelated composite `ρ
⊗ σ` is the sum of the entropies,

`S(ρ ⊗ σ) = S(ρ) + S(σ)`.
-/
theorem State.vonNeumannEntropy_tmul (ρ : State S) (σ : State T) :
    (ρ.tmul σ).vonNeumannEntropy = ρ.vonNeumannEntropy + σ.vonNeumannEntropy := sorry

end AxQM
