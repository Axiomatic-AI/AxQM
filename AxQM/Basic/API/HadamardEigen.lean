/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.PureState
import AxQM.Basic.API.Eigenstate
import AxQM.Basic.Observable
import Mathlib.Tactic.LinearCombination

/-!
# AxQM.Basic.API — eigenvalues and eigenvectors of the Hadamard gate

**Nielsen & Chuang, Exercise 2.53** (§2.2.2, p. 82) asks for the
eigenvalues and eigenvectors of `H`. The Hadamard gate `H = (1/√2)!![1,1;1,-1]`
is both unitary (Exercise 2.51, `hadamardGate : Evolution qubit`) and **Hermitian**, so it is a
legitimate `Observable qubit` — the primitive whose real spectrum is a set of measurement values.
Its eigenvalues are the possible measurement outcomes and its eigenvectors the corresponding
eigenstates, which is exactly what the exercise asks for. We therefore ground the eigendecomposition
in the `Observable` primitive.

## Main declarations
* the general eigenstate generator `Observable.HasEigenstate A μ ψ` — the predicate that the pure
  state `ψ` is an eigenstate of the observable `A` with real eigenvalue `μ`: `A ψ = μ ψ`.
* `hadamardObservable : Observable qubit` — the Hadamard gate as an observable, with the same
  operator as `hadamardGate`.
* `hadamardEigenstatePlus`, `hadamardEigenstateMinus : PureState qubit` — the normalized
  eigenstates.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

open Matrix Complex

variable {S : QSystem}

/-- The **Hadamard gate as an observable** on the qubit. Its `±1` spectrum is the content of
Exercise 2.53. -/
def hadamardObservable : Observable qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
  selfAdjoint :=
    Concrete.hadamardC_isHermitian.isSelfAdjoint.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))

/-- The unnormalized `+1`-eigenvector `(1, √2 − 1)` of `H`, as a qubit vector. -/
def hadamardEigenvecPlus : qubit := WithLp.toLp 2 ![1, (Real.sqrt 2 - 1 : ℂ)]

/-- The unnormalized `−1`-eigenvector `(√2 − 1, −1)` of `H`, as a qubit vector. -/
def hadamardEigenvecMinus : qubit := WithLp.toLp 2 ![(Real.sqrt 2 - 1 : ℂ), -1]

/-- `(1, √2−1)` is nonzero (its first component is `1`), so it is a genuine eigenvector. -/
theorem hadamardEigenvecPlus_ne_zero : hadamardEigenvecPlus ≠ 0 := by
  intro h
  have : (WithLp.ofLp hadamardEigenvecPlus) 0 = 0 := by rw [h]; rfl
  simp [hadamardEigenvecPlus, WithLp.ofLp_toLp] at this

/-- `(√2−1, −1)` is nonzero (its second component is `−1`), so it is a genuine eigenvector. -/
theorem hadamardEigenvecMinus_ne_zero : hadamardEigenvecMinus ≠ 0 := by
  intro h
  have : (WithLp.ofLp hadamardEigenvecMinus) 1 = 0 := by rw [h]; rfl
  simp [hadamardEigenvecMinus, WithLp.ofLp_toLp] at this

/-- The normalized `+1`-eigenstate `|h₊⟩` of the Hadamard observable, via the shared
`PureState.normalize`. -/
def hadamardEigenstatePlus : PureState qubit :=
  PureState.normalize hadamardEigenvecPlus hadamardEigenvecPlus_ne_zero

/-- The normalized `−1`-eigenstate `|h₋⟩` of the Hadamard observable, via the shared
`PureState.normalize`. -/
def hadamardEigenstateMinus : PureState qubit :=
  PureState.normalize hadamardEigenvecMinus hadamardEigenvecMinus_ne_zero

end AxQM
