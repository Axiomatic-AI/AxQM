/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringBasisChange

/-!
# Concrete: commutation of Pauli strings and the symplectic form (Nielsen & Chuang, Ex. 10.33)

It proves that any two `n`-fold
Pauli strings (`Concrete.pauliString`, indexed by `g : Fin n → Fin 4`) either **commute** or
**anticommute**, with the dichotomy governed entirely by the **binary symplectic form** of their
check-matrix rows. This is the algebraic heart of the stabilizer formalism — Nielsen & Chuang,
Exercise 10.33: two elements of the Pauli group commute iff `r(g) Λ r(g')ᵀ = 0 (mod 2)`, where
`r(·)` is the `(x | z)` check-matrix row and `Λ = [[0, I], [I, 0]]` is the symplectic form. Because
commutation is unchanged by the overall phase, the phase-free `pauliString` (which carries no `±1,
±i` prefactor) is the right representative for this fact.

## Main results
* `pauliString_mul_self` — each Pauli string is an **involution**, `P_g P_g = I` (so `P_g` is
  unitary / its own inverse).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

/-- The **X-bit** of a single-qubit Pauli index: `I, X, Y, Z ↦ 0, 1, 1, 0`. It is `1` exactly for
the Paulis (`X`, `Y`) that contain an `X` factor, i.e. the X-part of the binary symplectic
representation of a single-qubit Pauli. -/
def pauliXBit : Fin 4 → ℕ := ![0, 1, 1, 0]

/-- The **Z-bit** of a single-qubit Pauli index: `I, X, Y, Z ↦ 0, 0, 1, 1`. It is `1` exactly for
the Paulis (`Y`, `Z`) that contain a `Z` factor, i.e. the Z-part of the binary symplectic
representation of a single-qubit Pauli. -/
def pauliZBit : Fin 4 → ℕ := ![0, 0, 1, 1]

/-- The **single-qubit symplectic pairing** of two Pauli indices, `x_a z_b + z_a x_b`. It is the
per-qubit contribution to the symplectic form `r(g) Λ r(g')ᵀ`, and its parity is the single-qubit
commutation indicator: `0 (mod 2)` when `σ_a`, `σ_b` commute, `1` when they anticommute. -/
def singlePauliAnticomm (a b : Fin 4) : ℕ :=
  pauliXBit a * pauliZBit b + pauliZBit a * pauliXBit b

variable {n : ℕ}

/-- The **symplectic form** (total anticommutation pairing) of two Pauli strings, `Σ_k
singlePauliAnticomm (g k) (h k)`. This is `r(g) Λ r(g')ᵀ` for the check-matrix rows `r(g) = (x_g |
z_g)` and symplectic form `Λ = [[0, I], [I, 0]]`; its parity is the mod-2 quantity of Nielsen &
Chuang, Exercise 10.33. -/
def pauliAnticommCount (g h : Fin n → Fin 4) : ℕ := ∑ k, singlePauliAnticomm (g k) (h k)

/-- Each Pauli string is an **involution**: `P_g P_g = I`. In particular `P_g` is its own inverse,
hence unitary. -/
theorem pauliString_mul_self (g : Fin n → Fin 4) : pauliString g * pauliString g = 1 := by
  rw [pauliString_eq_kronFamily, kronFamily_mul]
  simp only [pauli_mul_self]
  exact kronFamily_one

end AxQM.Concrete
