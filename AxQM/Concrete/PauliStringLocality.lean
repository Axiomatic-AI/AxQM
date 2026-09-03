/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Concrete: locality of Pauli strings and the polynomial count of local terms

This file supplies the combinatorial
core behind **Nielsen & Chuang, Exercise 4.48**: *the restriction of each term `Hₖ` in a
Hamiltonian `H = Σₖ Hₖ` (eq. 4.97) to involve at most a constant `c` particles implies that the
number of terms `L` is upper bounded by a polynomial in the particle count `n`.*

## Main definitions

* `Concrete.pauliStringSupport g` — the support `{i | g i ≠ 0}` of the Pauli string `g`, the set
  of qubits it acts on non-trivially.
* `Concrete.localPauliStrings c n` — the Pauli strings on `n` qubits acting on at most `c`
  particles (support of size `≤ c`): the "menu" of `c`-local Hamiltonian terms.
-/

open Matrix
open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **support** of the Pauli string `g : Fin n → Fin 4`. The number of particles the
corresponding local term acts on is `(pauliStringSupport g).card`. -/
def pauliStringSupport (g : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.univ.filter (fun i => g i ≠ 0)

/-- The **`c`-local Pauli strings** on `n` qubits: those acting on at most `c` particles
(`(pauliStringSupport g).card ≤ c`). This is the menu of possible `c`-local Hamiltonian terms in
the Pauli picture — each `g` names a term `h_g · g` of a Hamiltonian `H = Σ_g h_g g`. -/
def localPauliStrings (c n : ℕ) : Finset (Fin n → Fin 4) :=
  Finset.univ.filter (fun g => (pauliStringSupport g).card ≤ c)

end AxQM.Concrete
