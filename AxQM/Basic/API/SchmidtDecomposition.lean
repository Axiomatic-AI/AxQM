/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.Matricization
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# AxQM — the Schmidt decomposition of a bipartite pure state (Nielsen–Chuang Theorem 2.7)

The **Schmidt decomposition** (N&C §2.5, Theorem 2.7): every pure state `|ψ⟩` of a composite
system `S ⊗ T` can be written in Schmidt form.

## Main results

* `AxQM.PureState.exists_schmidt_decomposition` — the Schmidt decomposition of a
  bipartite pure state.
* `AxQM.PureState.exists_schmidt_decomposition_card_le` — **Exercise 2.76**: the same
  decomposition with the number of Schmidt terms bounded by the *smaller* subsystem dimension,
  `n ≤ min S.dim T.dim` (the extension to unequal dimensions).
* `AxQM.PureState.IsSchmidtDecomposition` — the predicate "`(l, a, b)` is a (reduced)
  Schmidt decomposition of `ψ`".
* `AxQM.PureState.SameSchmidtCoeffs` — the predicate "`ψ` and `φ` have **identical Schmidt
  coefficients**" (a common strictly-positive coefficient family over orthonormal Schmidt bases),
  the hypothesis of **Exercise 2.80**.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Schmidt decomposition (Nielsen–Chuang Theorem 2.7).** Every bipartite pure state `|ψ⟩` of
`S ⊗ T` can be written as `∑ᵢ λᵢ |aᵢ⟩ ⊗ |bᵢ⟩` with strictly positive Schmidt coefficients `λᵢ`
over orthonormal families `aᵢ` in `S` and `bᵢ` in `T`, normalised to `∑ᵢ λᵢ² = 1`. -/
theorem PureState.exists_schmidt_decomposition (ψ : PureState (S ⊗ T)) :
    ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space),
      (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
      (∑ i, l i ^ 2 = 1) ∧ ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i := sorry

/-- **Schmidt decomposition for subsystems of possibly unequal dimension (Nielsen–Chuang Exercise
2.76).** Every bipartite pure state `ψ : PureState (S ⊗ T)` decomposes as `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`
(`exists_schmidt_decomposition`) with the number of Schmidt terms bounded by the *smaller* of
the two subsystem dimensions, `n ≤ min S.dim T.dim`.

It is a strict *strengthening* of `exists_schmidt_decomposition`, not a weakening.
-/
theorem PureState.exists_schmidt_decomposition_card_le (ψ : PureState (S ⊗ T)) :
    ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space),
      n ≤ min S.dim T.dim ∧ (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
      (∑ i, l i ^ 2 = 1) ∧ ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i := sorry

/-- **`(l, a, b)` is a Schmidt decomposition of the bipartite pure state `ψ`.** The data of a
Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` (Nielsen–Chuang Theorem 2.7), stated in reduced
form: strictly positive Schmidt coefficients `l : Fin n → ℝ`, orthonormal Schmidt bases `a : Fin
n → S.space` and `b : Fin n → T.space`, normalisation `∑ᵢ lᵢ² = 1`, and the identity `ψ.vec = ∑ᵢ
(lᵢ : ℂ) • aᵢ ⊗ₜ bᵢ`. Its fields are exactly the conclusion of
`PureState.exists_schmidt_decomposition`; naming the concept lets a *concrete* state's Schmidt
decomposition be a single, reusable claim (e.g. N&C Exercise 2.79). -/
def PureState.IsSchmidtDecomposition (ψ : PureState (S ⊗ T)) {n : ℕ}
    (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space) : Prop :=
  (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
    (∑ i, l i ^ 2 = 1) ∧ ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i

/-- **Two bipartite pure states have identical Schmidt coefficients** (the hypothesis of
Nielsen–Chuang Exercise 2.80).

Since the Schmidt coefficients are the (uniquely determined) nonzero singular values of the
matricized state, this existential — a common *ordered* coefficient family `l` — holds exactly
when `ψ` and `φ` have the same Schmidt coefficients as a multiset: given equal multisets,
permute one decomposition's index to match the other. So the predicate is a faithful rendering
of "identical Schmidt coefficients", neither stronger nor weaker. -/
def PureState.SameSchmidtCoeffs (ψ φ : PureState (S ⊗ T)) : Prop :=
  ∃ (n : ℕ) (l : Fin n → ℝ) (a a' : Fin n → S.space) (b b' : Fin n → T.space),
    (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧ Orthonormal ℂ a' ∧ Orthonormal ℂ b' ∧
      ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i ∧ φ.vec = ∑ i, (l i : ℂ) • a' i ⊗ₜ[ℂ] b' i

end AxQM
