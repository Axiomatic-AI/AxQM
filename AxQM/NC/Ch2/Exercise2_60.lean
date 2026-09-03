/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliEigen

/-!
# Nielsen & Chuang, Exercise 2.60 (eigenvalues and eigenprojectors of `v⃗ · σ⃗`)

*(N&C p. 90.)*

Show v.sigma has eigenvalues ±1 and projectors P±=(I±v.sigma)/2.

* `pauliObservable_hasEigenstate_one` — `v⃗·σ⃗` genuinely has `+1` and `−1` as eigenvalues (each
  exhibits an eigenstate).
* `pauliObservable_hasEigenstate_neg_one`
* `pauliObservable_eigenvalue_eq_one_or_neg_one` — exhaustiveness: *every* eigenvalue of `v⃗·σ⃗` is
  `+1` or `−1`.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.60 (`+1`).** For a unit vector `v⃗`, the spin observable
`v⃗ · σ⃗` has `+1` as an eigenvalue: there is a pure state `ψ` with `(v⃗·σ⃗) ψ = ψ`. -/
theorem pauliObservable_hasEigenstate_one {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    ∃ ψ : PureState qubit, (pauliObservable v).HasEigenstate 1 ψ := sorry

/-- **Nielsen & Chuang, Exercise 2.60 (`−1`).** For a unit vector `v⃗`, the spin observable
`v⃗ · σ⃗` has `−1` as an eigenvalue: there is a pure state `ψ` with `(v⃗·σ⃗) ψ = −ψ`. -/
theorem pauliObservable_hasEigenstate_neg_one {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    ∃ ψ : PureState qubit, (pauliObservable v).HasEigenstate (-1) ψ := sorry

/-- **Nielsen & Chuang, Exercise 2.60 (exhaustiveness).** For a unit vector `v⃗`, every eigenvalue
of the spin observable `v⃗ · σ⃗` is `+1` or `−1`: if some pure state `ψ` is a `μ`-eigenstate
then `μ = 1` or `μ = −1`. -/
theorem pauliObservable_eigenvalue_eq_one_or_neg_one {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (μ : ℝ) (ψ : PureState qubit)
    (h : (pauliObservable v).HasEigenstate μ ψ) : μ = 1 ∨ μ = -1 := sorry

end AxQM
