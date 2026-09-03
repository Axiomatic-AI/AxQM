/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardEigen

/-!
# Nielsen & Chuang, Exercise 2.53 (eigenvalues and eigenvectors of the Hadamard gate)

*(N&C p. 82.)*

What are the eigenvalues and eigenvectors of H?

* `hadamardObservable_hasEigenstate_one`, `hadamardObservable_hasEigenstate_neg_one` — `|h₊⟩`,
  `|h₋⟩` are eigenstates with eigenvalues `+1`, `−1`;
* `hadamardObservable_eigenvalue_eq_one_or_neg_one` — exhaustiveness: *every* eigenvalue of `H` is
  `+1` or `−1`, so together with the two witnesses the eigenvalues are exactly `{+1, −1}`.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.53 (`+1`).** `|h₊⟩ ∝ (1, √2 − 1)` is an eigenstate of the
Hadamard observable with eigenvalue `+1`: `H |h₊⟩ = |h₊⟩`. -/
theorem hadamardObservable_hasEigenstate_one :
    hadamardObservable.HasEigenstate 1 hadamardEigenstatePlus := sorry

/-- **Nielsen & Chuang, Exercise 2.53 (`−1`).** `|h₋⟩ ∝ (√2 − 1, −1)` is an eigenstate of the
Hadamard observable with eigenvalue `−1`: `H |h₋⟩ = −|h₋⟩`. -/
theorem hadamardObservable_hasEigenstate_neg_one :
    hadamardObservable.HasEigenstate (-1) hadamardEigenstateMinus := sorry

/-- **Nielsen & Chuang, Exercise 2.53 (exhaustiveness).** The eigenvalues of the Hadamard observable
are *exactly* `±1`: every real `μ` for which some pure state is a `μ`-eigenstate satisfies `μ =
1` or `μ = −1`. -/
theorem hadamardObservable_eigenvalue_eq_one_or_neg_one (μ : ℝ) (ψ : PureState qubit)
    (h : hadamardObservable.HasEigenstate μ ψ) : μ = 1 ∨ μ = -1 := sorry

end AxQM
