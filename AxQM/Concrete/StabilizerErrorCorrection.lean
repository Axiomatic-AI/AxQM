/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerCodeProjector
import AxQM.Concrete.StabilizerCodeDimension
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumErrorCorrection
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Concrete: error-correction conditions for stabilizer codes (Nielsen & Chuang, Theorem 10.8)

Nielsen & Chuang **Theorem 10.8**: the *error-correction conditions for stabilizer codes*
(p. 466).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Nielsen & Chuang, Theorem 10.8** (error-correction conditions for stabilizer codes). -/
theorem codeProjector_isCorrectableErrorSet {ι : Type} [Fintype ι]
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S) (E : ι → PauliGroup n)
    (hE : ∀ j k, ¬ ((E j)⁻¹ * E k ∈ Subgroup.normalizer S ∧ (E j)⁻¹ * E k ∉ S)) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (E i).toMat) R := sorry

end AxQM.Concrete
