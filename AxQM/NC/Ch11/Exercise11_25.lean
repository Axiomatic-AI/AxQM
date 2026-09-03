/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.Theorem11_15
import AxQM.Basic.API.EntropyJointTheorem
import AxQM.Basic.API.Qudit
import AxQM.Core.ConditionalEntropy

/-!
# N&C Exercise 11.25 — concavity of the conditional entropy from strong subadditivity

*(N&C p. 521.)*

Show concavity of the quantum conditional entropy follows from strong subadditivity.

* `condVonNeumannEntropy_concave` — `∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {A B : QSystem}

/-- **Concavity of the quantum conditional entropy** (Nielsen & Chuang, Corollary 11.13; Exercise
11.25). For a probability distribution `p` and a family of states `ρ : ι → State (A ⊗ B)`, the
conditional entropy `S(A|B) = S(A,B) − S(B)` satisfies

`∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`.
-/
theorem State.condVonNeumannEntropy_concave {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State (A ⊗ B)) :
    ∑ i, p i * (ρ i).condVonNeumannEntropy
      ≤ (State.mix p hp hsum ρ).condVonNeumannEntropy := sorry

end AxQM
