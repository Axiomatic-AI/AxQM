/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.Matrix.PolarDecomposition
import Mathlib.Tactic

/-!
# Alberti's alternate characterization of the fidelity (Nielsen & Chuang, Problem 9.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 9.1
(p. 423) asks to show the "alternate characterization of the fidelity", N&C
equation `(9.145)`:
```
F(ρ, σ) = inf_P tr(ρ P) tr(σ P⁻¹),
```
where `F(ρ, σ) = tr √(√ρ σ √ρ)` is N&C's fidelity (their `(9.53)`, the
*square-root* fidelity, with `F(ρ, ρ) = 1` and `F(|ψ⟩, |ϕ⟩) = |⟨ψ|ϕ⟩|`) and the
infimum ranges over invertible positive matrices `P`.

## Main definitions and statements

* `matrixFidelity` — N&C's fidelity formula `F(ρ, σ) = tr √(√ρ σ √ρ)` on
  matrices, the quantity `(9.145)` is about.
* `albertiProduct` — the functional `P ↦ tr(ρ P) tr(σ P⁻¹)` of `(9.145)`.
* `rhoEx`, `sigmaEx` — the two diagonal states `ρ = diag(9/10, 1/10)` and
  `σ = diag(1/10, 9/10)`.
* `fidelity_not_lower_bound_of_albertiProduct` — **the refutation of N&C
  `(9.145)`**: there is an *invertible positive* (`PosDef`) `P` with
  `tr(ρ P) tr(σ P⁻¹) < F(ρ, σ)`, so `F(ρ, σ)` is not a lower bound of the
  functional over `(9.145)`'s index set and cannot equal the infimum. The
  correct statement (Alberti's theorem) has `F(ρ, σ)²` on the left.
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-- **Nielsen & Chuang fidelity formula on matrices** (their `(9.53)`):
`F(ρ, σ) = tr √(√ρ σ √ρ)`. For density matrices `ρ, σ` the matrix `√ρ σ √ρ` is
positive semidefinite, so its continuous-functional-calculus square root has a
nonnegative trace. This is the quantity Nielsen & Chuang's Problem 9.1
(`(9.145)`) is about. -/
noncomputable def matrixFidelity {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℝ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace

/-- The functional `P ↦ tr(ρ P) tr(σ P⁻¹)` appearing on the right-hand side of
Nielsen & Chuang `(9.145)`. The infimum of this functional over invertible
positive `P` is, by Alberti's theorem, `F(ρ, σ)²`. -/
noncomputable def albertiProduct {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ P : Matrix n n ℝ) : ℝ :=
  (ρ * P).trace * (σ * P⁻¹).trace

/-- The eigenvalue vector of the first density matrix, `ρ = diag(9/10, 1/10)`. -/
noncomputable def rhoDiagVec : Fin 2 → ℝ := ![9 / 10, 1 / 10]

/-- The eigenvalue vector of the second density matrix, `σ = diag(1/10, 9/10)`. -/
noncomputable def sigmaDiagVec : Fin 2 → ℝ := ![1 / 10, 9 / 10]

/-- The first density matrix, `ρ = diag(9/10, 1/10)`. -/
noncomputable def rhoEx : Matrix (Fin 2) (Fin 2) ℝ := diagonal rhoDiagVec

/-- The second density matrix, `σ = diag(1/10, 9/10)`. -/
noncomputable def sigmaEx : Matrix (Fin 2) (Fin 2) ℝ := diagonal sigmaDiagVec

/-- **Refutation of Nielsen & Chuang `(9.145)`.** If the fidelity equalled the infimum `inf_P tr(ρ
P) tr(σ P⁻¹)` over invertible positive `P`, then in particular `F(ρ, σ)` would be a *lower
bound* of `P ↦ tr(ρ P) tr(σ P⁻¹)` **on that index set**. It is not. Hence the printed identity
`(9.145)` is false; the correct statement (Alberti's theorem) has `F(ρ, σ)²` on the left.
-/
theorem fidelity_not_lower_bound_of_albertiProduct :
    ¬ ∀ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef →
      matrixFidelity rhoEx sigmaEx ≤ albertiProduct rhoEx sigmaEx P := sorry

end AxQM.Concrete
