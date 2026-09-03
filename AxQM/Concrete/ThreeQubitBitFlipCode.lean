/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Concrete: the combinatorics of the three-qubit bit-flip code (Nielsen & Chuang, §10.1.1)

The three-qubit bit-flip code encodes `|0⟩ ↦ |000⟩`, `|1⟩ ↦ |111⟩`; error-correction against
single bit-flip errors is a *majority vote* on the three physical qubits. This file develops the
underlying **combinatorics** on the eight computational-basis labels, identified with the finite
type `Fin 8` under the big-endian convention.

## Contents

* `xorPerm m` — the permutation `x ↦ x ⊕ m` of `Fin 8` (bitwise XOR by the mask `m : Fin 8`). A
  bit-flip error on a *subset* of the qubits is `xorPerm m` for the subset's bitmask `m`; the three
  single-qubit flips are `xorPerm 4`, `xorPerm 2`, `xorPerm 1`. It is an involution, so every
  error is its own inverse — the reason a bit flip is undone by re-applying it.
* `errorMask j` — the bitmask of the single-qubit error diagnosed by syndrome `j : Fin 4`:
  `0 ↦ 0` (no error), `1 ↦ 4`, `2 ↦ 2`, `3 ↦ 1` (flip qubit `j`).
* `syndrome x` — the error syndrome read off a computational-basis outcome `x`: `0` for the
  codewords `000, 111`, and the position `j ∈ {1,2,3}` of the *minority* qubit otherwise
  (majority-vote decoding).
-/

namespace AxQM.Concrete

/-- **The bitwise-XOR permutation** `xorPerm m : Equiv.Perm (Fin 8)`, `x ↦ x ⊕ m`. A bit-flip error
on the subset of the three qubits picked out by the bitmask `m` acts on the computational basis
by this permutation; the single-qubit flips are `xorPerm 4`, `xorPerm 2`, `xorPerm 1` (masks
`100, 010, 001`). -/
def xorPerm (m : Fin 8) : Equiv.Perm (Fin 8) where
  toFun x := ⟨x.1 ^^^ m.1, Nat.xor_lt_two_pow (n := 3) x.2 m.2⟩
  invFun x := ⟨x.1 ^^^ m.1, Nat.xor_lt_two_pow (n := 3) x.2 m.2⟩
  left_inv x := by ext; simp [Nat.xor_assoc]
  right_inv x := by ext; simp [Nat.xor_assoc]

/-- The **single-qubit error masks** indexed by syndrome value `j : Fin 4`: syndrome `0` is no
error (`mask 0`), and syndrome `j ∈ {1,2,3}` is the flip of qubit `j`, with masks `4, 2, 1`
(big-endian). -/
def errorMask : Fin 4 → Fin 8 := ![0, 4, 2, 1]

/-- **The error syndrome of a computational-basis outcome** `x : Fin 8`. It is `0` on the two
codewords `000` (`0`) and `111` (`7`), and otherwise the position `j ∈ {1,2,3}` of the single
minority qubit — the majority-vote diagnosis "bit `j` flipped". Explicitly
`[0, 3, 2, 1, 1, 2, 3, 0]` on `0, …, 7`. -/
def syndrome : Fin 8 → Fin 4 := ![0, 3, 2, 1, 1, 2, 3, 0]

end AxQM.Concrete
