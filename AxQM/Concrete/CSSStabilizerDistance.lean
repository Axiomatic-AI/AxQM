/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CSSStabilizerSubgroup
import AxQM.Concrete.PauliSubgroupNormalizer
import AxQM.Concrete.StabilizerCodeDistance

/-!
# Concrete: the distance and `t`-qubit correction of the CSS code `CSS(C₁, C₂)`

It completes the error-correction half of **Nielsen & Chuang, Exercise 10.51** — *the check matrix
(10.106) is the stabilizer of the CSS code `CSS(C₁, C₂)`, and Theorem 10.8 gives `t`-qubit
correction* (p. 470).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The CSS stabilizer is finite (a subgroup of the finite Pauli group `Gₙ`), as Theorem 10.8's code
projector and correction require. -/
noncomputable instance {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} :
    Fintype ↥(cssStabilizer C₁ C₂) := Fintype.ofFinite _

/-- **CSS(C₁, C₂) corrects arbitrary errors on up to `t` qubits** (Nielsen & Chuang, Exercise
10.51).
-/
theorem cssStabilizer_isCorrectableErrorSet_of_correctsErrors
    {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁) {t : ℕ}
    (h1 : C₁.CorrectsErrors t) (h2 : C₂.dual.CorrectsErrors t) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2)
          (codeProjector (cssStabilizer C₁ C₂))).Corrects
        (fun i : {p : PauliGroup n // p.weight ≤ t} =>
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (i.val).toMat) R := sorry

end AxQM.Concrete
