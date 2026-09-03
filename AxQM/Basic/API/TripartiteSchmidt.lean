/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellState
import AxQM.Concrete.PauliEigenvectors
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM — no single-Schmidt-basis decomposition for tripartite states (N&C Exercise 2.77)

Nielsen & Chuang, Exercise 2.77 (p. 110): *there exist* pure states `|ψ⟩` of a three-component
system `ABC` which **cannot** be written in the "single Schmidt basis" (triorthogonal) form.

## Main results

* `PureState.HasTriorthogonalDecomposition` — the tripartite "single Schmidt basis" form.
* `zeroTensorBell` — the counterexample `|0⟩ ⊗ |Φ⁺⟩`.
* `zeroTensorBell_not_hasTriorthogonalDecomposition` — it has no such decomposition.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **A "single Schmidt basis" (triorthogonal) decomposition** of a tripartite pure state. This is
the tripartite analogue of the Schmidt form of Theorem 2.7; N&C Exercise 2.77 asks to show it
does not always exist. (Stated with orthonormal *families*, which subsumes N&C's orthonormal
*bases*.) -/
def PureState.HasTriorthogonalDecomposition (ψ : PureState (A ⊗ (B ⊗ C))) : Prop :=
  ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → A.space) (b : Fin n → B.space) (c : Fin n → C.space),
    Orthonormal ℂ a ∧ Orthonormal ℂ b ∧ Orthonormal ℂ c ∧
    ψ.vec = ∑ i, (l i : ℂ) • (a i ⊗ₜ[ℂ] (b i ⊗ₜ[ℂ] c i))

/-- **The counterexample `|0⟩ ⊗ |Φ⁺⟩`** (N&C Exercise 2.77): the first qubit in the
computational-basis state `|0⟩`, the last two maximally entangled in the Bell state `|Φ⁺⟩`. A pure
state of `qubit ⊗ (qubit ⊗ qubit)` with no triorthogonal decomposition. -/
def zeroTensorBell : PureState (qubit ⊗ (qubit ⊗ qubit)) := qubitBasis 0 ⊗ bellPhiPlus

/-- **Nielsen & Chuang, Exercise 2.77.** The tripartite state `|0⟩ ⊗ |Φ⁺⟩` has no "single Schmidt
basis" decomposition `∑ᵢ λᵢ (aᵢ ⊗ bᵢ ⊗ cᵢ)` — the Schmidt decomposition has no tripartite
analogue. -/
theorem zeroTensorBell_not_hasTriorthogonalDecomposition :
    ¬ zeroTensorBell.HasTriorthogonalDecomposition := sorry

end AxQM
