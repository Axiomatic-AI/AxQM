/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerErrorCorrection
import AxQM.Concrete.PauliStringLocality

/-!
# Concrete: weight, distance, and correcting located errors (Nielsen & Chuang, Exercise 10.45)

Nielsen & Chuang, **Exercise 10.45** (*correcting located errors*, p. 467): the weight of a Pauli
operator, the distance of a stabilizer code, and the correctability of errors on a known set of
affected qubits.
-/

open Matrix
open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **weight** of a Pauli-group element `p ∈ Gₙ` (Nielsen & Chuang §10.5.5): the number of
tensor factors of `p` that are not the identity, i.e. the cardinality of the support of its
underlying Pauli string `p.idx`. The overall phase `iˢ` does not affect the weight; e.g.
`weight (X₁ Z₄ Y₈) = 3`. -/
def PauliGroup.weight (p : PauliGroup n) : ℕ := (pauliStringSupport p.idx).card

/-- The **distance** of a stabilizer code `C(S)` (Nielsen & Chuang §10.5.5): the minimum weight of a
nontrivial logical operator, taken in `ℕ∞ = WithTop ℕ`. A nontrivial logical operator is an
element `p ∈ N(S)` that is not a phase multiple of any stabilizer element (`∀ s' ∈ S, p.idx ≠
s'.idx`) — N&C's `N(S) − S` read modulo the global phase, i.e. `N(S) \ ⟨iI, S⟩`. Using `ℕ∞`
handles the trivial case where there are no such operators (e.g. `k = 0`), for which the infimum
over the empty set is `⊤`. -/
noncomputable def stabilizerCodeDistance (S : Subgroup (PauliGroup n)) : ℕ∞ :=
  ⨅ p ∈ {p : PauliGroup n | p ∈ Subgroup.normalizer S ∧ ∀ s' ∈ S, p.idx ≠ s'.idx},
    (p.weight : ℕ∞)

/-- **Nielsen & Chuang, Exercise 10.45** (correcting located errors). Let `S` be a stabilizer (`-I ∉
S`) for a code `C(S)`, and let `L` be a *known* set of affected qubit positions whose size is
strictly below the code distance, `|L| < stabilizerCodeDistance S` (for an `[n, k, d]` code and
the exercise's `|L| = d − 1` this is `d − 1 < d`). Then the family of **all Pauli errors
supported on `L`** (elements of `Gₙ` acting as the identity off `L`) is a **correctable set of
errors** for `C(S)`: there is a trace-preserving recovery `R` (`∑ₒ Rₒ† Rₒ = 1`) correcting every
such error.
-/
theorem locatedPauliErrors_isCorrectableErrorSet
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S)
    (L : Finset (Fin n)) (hL : (L.card : ℕ∞) < stabilizerCodeDistance S) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i : {p : PauliGroup n // pauliStringSupport p.idx ⊆ L} =>
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (i.val).toMat) R := sorry

/-- **Exercise 10.45 for an `[n, k, d]` code.** The specialization to the textbook's parameters: a
stabilizer `S` (`-I ∉ S`) whose code has distance at least `d` (`(d : ℕ∞) ≤
stabilizerCodeDistance S`, in particular any `[n, k, d]` code), and a known set `L` of affected
qubits with fewer than `d` of them (`|L| < d`, i.e. at most `d − 1` — the exercise's
hypothesis), admits a recovery correcting all Pauli errors located on `L`. -/
theorem locatedPauliErrors_isCorrectableErrorSet_of_dist_ge
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S)
    {d : ℕ} (hdist : (d : ℕ∞) ≤ stabilizerCodeDistance S)
    (L : Finset (Fin n)) (hL : L.card < d) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i : {p : PauliGroup n // pauliStringSupport p.idx ⊆ L} =>
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (i.val).toMat) R := sorry

end AxQM.Concrete
