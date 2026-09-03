/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyOrthogonalMixture
import AxQM.Basic.API.EntropyMixtureReverse
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.API.ArakiLiebEqualityConditions
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Entropy
import AxQM.NC.Ch2.Exercise2_74
import AxQM.NC.Ch11.Theorem11_10

/-!
# Nielsen & Chuang, Exercise 11.16 — equality conditions for the triangle inequality

*(N&C p. 516.)*

Equality conditions for triangle inequality S(A,B)=S(B)-S(A) via eigenbasis/support.

* `vonNeumannEntropy_mix_eq_reducedRight_sub_reducedLeft_iff`
* `halfHalf`
* `halfHalf_nonneg`
* `halfHalf_sum`
* `classicalCorrKet`
* `classicalCorrQubits`
* `classicalCorr_arakiLieb_condition_not_sufficient`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ## The corrected equality condition (the intended statement of Exercise 11.16) -/

/-- **Nielsen & Chuang, Exercise 11.16, corrected.** Let `ρ^{AB} = ∑ᵢ λᵢ |i⟩⟨i|` be a (reduced)
spectral decomposition of a bipartite state — the eigenvectors `|i⟩` orthonormal, recorded here as
pairwise **orthogonal supports** of the pure eigenprojectors `|i⟩⟨i|` (`hψ`, equivalent to
orthonormality for unit vectors), with strictly positive eigenvalues `λᵢ > 0` (`hpos`). Then the
Araki–Lieb triangle inequality is saturated,

`S(A,B) = S(B) − S(A)`,

**if and only if**

* the left marginals `ρ^A_i = tr_B(|i⟩⟨i|)` are all **equal** (`∀ i j, ρ^A_i = ρ^A_j`), and
* the right marginals `ρ^B_i = tr_A(|i⟩⟨i|)` have pairwise **orthogonal support**.

This is the statement Exercise 11.16 evidently intends. It differs from the **printed** exercise
only in the first condition: N&C requires the `ρ^A_i` merely to share a common eigenbasis, but that
is too weak — equality forces the `ρ^A_i` to be *identical*, strictly stronger than a common
eigenbasis. The counterexample `classicalCorrQubits` below satisfies the printed conditions yet not
this equality. We take the *reduced* decomposition (`hpos`); a zero eigenvalue contributes nothing
to any of the three entropies, so its (arbitrary) eigenvector's marginals are physically
irrelevant.
-/
theorem State.vonNeumannEntropy_mix_eq_reducedRight_sub_reducedLeft_iff
    {A B : QSystem} {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hpos : ∀ i, 0 < lam i) (ψ : Fin n → PureState (A ⊗ B))
    (hψ : State.OrthogonalSupports fun i => (ψ i).toState) :
    (State.mix lam hlam hsum fun i => (ψ i).toState).vonNeumannEntropy
        = (State.mix lam hlam hsum fun i => (ψ i).toState).reducedRight.vonNeumannEntropy
          - (State.mix lam hlam hsum fun i => (ψ i).toState).reducedLeft.vonNeumannEntropy
      ↔ (∀ i j, (ψ i).toState.reducedLeft = (ψ j).toState.reducedLeft) ∧
          State.OrthogonalSupports fun i => (ψ i).toState.reducedRight := sorry

/-- The uniform two-outcome probability distribution `p₀ = p₁ = ½` on `Fin 2`, the mixing weights of
the counterexample state. -/
private def halfHalf : Fin 2 → ℝ := fun _ => 1 / 2

private theorem halfHalf_nonneg (i : Fin 2) : 0 ≤ halfHalf i := by unfold halfHalf; norm_num

private theorem halfHalf_sum : ∑ i, halfHalf i = 1 := by
  simp [halfHalf]

/-- **The `i`-th eigenvector `|ii⟩` of the counterexample state**: the computational-basis product
state `|i⟩ ⊗ |i⟩` of two qubits. The two vectors `|00⟩`, `|11⟩` are orthonormal, so
`classicalCorrQubits = ½|00⟩⟨00| + ½|11⟩⟨11|` is a spectral decomposition with these as
eigenvectors. -/
def classicalCorrKet (i : Fin 2) : PureState (qubit ⊗ qubit) := (qubitBasis i).tmul (qubitBasis i)

/-- **The maximally classically-correlated two-qubit state** `ρ^{AB} = ½|00⟩⟨00| + ½|11⟩⟨11|` — the
counterexample to the printed form of Nielsen & Chuang Exercise 11.16. It is the uniform mixture of
the two orthonormal pure states `|00⟩`, `|11⟩` (`classicalCorrKet`). -/
def classicalCorrQubits : State (qubit ⊗ qubit) :=
  State.mix halfHalf halfHalf_nonneg halfHalf_sum (fun i => (classicalCorrKet i).toState)

/-- **Refutation of Nielsen & Chuang Exercise 11.16 as printed.** The two stated conditions — the
`ρ^A_i` have a common eigenbasis, and the `ρ^B_i` have orthogonal support — both hold for
`classicalCorrQubits = ½|00⟩⟨00| + ½|11⟩⟨11|`, yet `S(A,B) ≠ S(B) − S(A)`. Hence the "`⟸`"
direction of the printed biconditional fails: a common eigenbasis for the `ρ^A_i` is *not*
sufficient (identical `ρ^A_i` is the correct condition). -/
theorem classicalCorr_arakiLieb_condition_not_sufficient :
    State.HasCommonEigenbasis (fun i => (classicalCorrKet i).toState.reducedLeft) ∧
      State.OrthogonalSupports (fun i => (classicalCorrKet i).toState.reducedRight) ∧
      classicalCorrQubits.vonNeumannEntropy
        ≠ classicalCorrQubits.reducedRight.vonNeumannEntropy
          - classicalCorrQubits.reducedLeft.vonNeumannEntropy := sorry

end AxQM
