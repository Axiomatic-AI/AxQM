/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringLocality
import AxQM.Basic.API.PauliTrotter

/-!
# Nielsen & Chuang, Exercise 4.48 — local Hamiltonians have polynomially many terms

*(N&C p. 207.)*

Show restricting each H_k to at most c particles bounds L polynomially in n.

* `exists_polynomial_pauliStringHamiltonian_card_le` — a literal `Polynomial ℕ` bound: for fixed
  locality `c` there is a single polynomial `p` (of degree `c`, independent of `n` and of the
  coefficients) bounding the number of `c`-local term `Observable`s by `p.eval n`.
-/

open scoped BigOperators

namespace AxQM

/-- **Exercise 4.48, "`L` is upper bounded by a polynomial in `n`".** For a fixed locality bound
`c` there is a single polynomial `p : Polynomial ℕ` (of degree `c`, independent of both the
particle count `n` and the coefficients `h`) such that, for every `n` and
every coefficient assignment `h`, the `c`-local Pauli-string Hamiltonian terms on the `n`-qubit
register are contained in a finite set of `Observable`s of cardinality at most `p.eval n`. This is
the literal reading of the exercise: the number of terms `L` is bounded by a polynomial in `n`. -/
theorem exists_polynomial_pauliStringHamiltonian_card_le (c : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (n : ℕ) (h : (Fin n → Fin 4) → ℝ),
      ∃ T : Finset (Observable (qudit (2 ^ n))),
        (∀ g : Fin n → Fin 4, (Concrete.pauliStringSupport g).card ≤ c →
          pauliStringHamiltonian g (h g) ∈ T) ∧
        T.card ≤ p.eval n := sorry

end AxQM
