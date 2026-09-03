/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The cyclic multiplication permutation of a finite field (N&C Problem 7.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 7.1 (p. 346, Efficient
temporal labeling) asks for circuits of only `O(poly(n))` gates that cyclically permute the diagonal
populations of a `2ⁿ × 2ⁿ` diagonal density matrix while leaving the `|0ⁿ⟩⟨0ⁿ|` population
fixed. Reading the diagonal populations as the computational-basis labels
`0, 1, …, 2ⁿ − 1`, this asks for a reversible circuit whose induced basis permutation fixes `0` and
cyclically permutes the `2ⁿ − 1` non-zero labels as a single long cycle, with a gate count
polynomial in `n`.

## Contents

* `GaloisField.exists_linear_isCycle_perm_transvecCount` — the **affirmative answer**: such an `L`
  is realised by a circuit of at most `2n²` transvections (`CNOT` gates), i.e.
  `LinearMap.toMatrix b b L = (T.map toMatrix).prod` with `T.length ≤ 2 * n²`.
-/

@[expose] public section

open Equiv

namespace GaloisField

open Matrix Matrix.TransvectionStruct in
/-- **N&C Problem 7.1 (Efficient temporal labeling), affirmative answer with the efficiency bound.**
For `n ≥ 2` there is an `𝔽₂`-linear permutation `L` of `GF(2ⁿ)`, a basis `b` of `GF(2ⁿ)` over `𝔽₂`
(indexed by `Fin n`, since `GF(2ⁿ)` is `n`-dimensional), and a list `T` of transvections with

* `L` **fixes `0`** and **cyclically permutes the `2ⁿ − 1` non-zero elements** (`IsCycle`,
  transitive on the non-zeros), and
* the matrix of `L` in the basis `b` equal to the product of the transvections in `T`, with
  `T.length ≤ 2n²`.
-/
theorem exists_linear_isCycle_perm_transvecCount (n : ℕ) (hn : 2 ≤ n) :
    ∃ (L : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n)
      (b : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n))
      (T : List (TransvectionStruct (Fin n) (ZMod 2))),
      L 0 = 0 ∧ Equiv.Perm.IsCycle L.toEquiv ∧
        (∀ x y : GaloisField 2 n, x ≠ 0 → y ≠ 0 → ∃ k : ℕ, (L.toEquiv ^ k) x = y) ∧
        LinearMap.toMatrix b b L.toLinearMap = (T.map toMatrix).prod ∧ T.length ≤ 2 * n ^ 2 := sorry

open Asymptotics Filter in
/-- The temporal-labeling gate-count bound `2n²` is `O(n²)`. -/
theorem transvecCount_isBigO_sq :
    (fun n : ℕ => ((2 * n ^ 2 : ℕ) : ℝ)) =O[atTop] fun n => (n : ℝ) ^ 2 := sorry

end GaloisField
