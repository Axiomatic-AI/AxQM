/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrix representations depend on the chosen bases (Nielsen & Chuang, Exercise 2.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.2
(p. 64, "Matrix representations: example") takes a two-dimensional space `V` with
basis vectors `|0⟩`, `|1⟩` and the linear operator `A` determined by
`A|0⟩ = |1⟩`, `A|1⟩ = |0⟩`. It asks to (1) give the matrix representation of `A`
with respect to the input and output basis `|0⟩, |1⟩`, and (2) exhibit input and
output bases giving a *different* matrix representation of the same `A`.
-/

namespace AxQM.Concrete

open scoped Matrix

noncomputable section

/-- The standard (computational) basis `|0⟩, |1⟩` of `ℂ² = EuclideanSpace ℂ (Fin 2)`, as a
`Module.Basis`. -/
def compBasis : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis

/-- **Nielsen & Chuang, Exercise 2.2**, the operator `A`. -/
def swapOperator : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  compBasis.constr ℂ ![compBasis 1, compBasis 0]

/-- **Part 1.** The matrix representation of `A` with respect to the standard
basis `|0⟩, |1⟩` for both the input and the output is `!![0, 1; 1, 0]`. -/
theorem toMatrix_swapOperator_std :
    LinearMap.toMatrix compBasis compBasis swapOperator = !![0, 1; 1, 0] := sorry

/-- The family `{|0⟩ + |1⟩, |0⟩ - |1⟩}` is linearly independent. -/
theorem hadamardFamily_linearIndependent :
    LinearIndependent ℂ ![compBasis 0 + compBasis 1, compBasis 0 - compBasis 1] := by
  have hb : LinearIndependent ℂ ![compBasis 0, compBasis 1] := by
    have h := compBasis.linearIndependent
    have he : (![compBasis 0, compBasis 1] : Fin 2 → EuclideanSpace ℂ (Fin 2)) = compBasis := by
      funext i; fin_cases i <;> simp
    rw [he]; exact h
  rw [LinearIndependent.pair_iff] at hb ⊢
  intro s t h
  obtain ⟨h1, h2⟩ := hb (s + t) (s - t) (by rw [← h]; module)
  exact ⟨by linear_combination (h1 + h2) / 2, by linear_combination (h1 - h2) / 2⟩

/-- A *different* basis of `ℂ²`: the unnormalised `|±⟩` basis
`{|0⟩ + |1⟩, |0⟩ - |1⟩}`. -/
def hadamardBasis : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  basisOfLinearIndependentOfCardEqFinrank hadamardFamily_linearIndependent
    (by simp [Module.finrank_eq_card_basis compBasis])

/-- **Part 2.** The matrix representation of the *same* operator `A` with respect
to the basis `{|0⟩ + |1⟩, |0⟩ - |1⟩}` for both input and output is the diagonal
matrix `!![1, 0; 0, -1]`. -/
theorem toMatrix_swapOperator_hadamard :
    LinearMap.toMatrix hadamardBasis hadamardBasis swapOperator = !![1, 0; 0, -1] := sorry

/-- The two matrix representations of `A` are different, so these bases genuinely
give rise to a different matrix representation, as Exercise 2.2 asks. -/
theorem toMatrix_swapOperator_std_ne_hadamard :
    LinearMap.toMatrix compBasis compBasis swapOperator
      ≠ LinearMap.toMatrix hadamardBasis hadamardBasis swapOperator := sorry

end

end AxQM.Concrete
