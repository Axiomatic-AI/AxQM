/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.Convex.Majorization

/-!
# Real vectors with identical non-zero entries

For finitely-indexed real families `x : ι → ℝ` and `y : κ → ℝ` we record the relation `SameNonzero x
y`: the two families have *identical non-zero entries*, i.e. the multiset of non-zero values of `x`
equals that of `y`. The index types `ι` and `κ` may differ, so this captures equality up to a
permutation of the entries and the insertion or deletion of zeros — Nielsen and Chuang's `≅`
relation on vectors (*Quantum Computation and Quantum Information*, Ex. 12.22).

## Main definitions

* `nonzeroEntries x`: the multiset of non-zero values `x i` (with multiplicity).
* `SameNonzero x y`: `nonzeroEntries x = nonzeroEntries y`.

## Tags

majorization, multiset, spectrum
-/

public section

open Finset
open scoped BigOperators

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

open scoped Classical in
/-- The multiset of *non-zero* entries of a finitely-indexed real family `x : ι → ℝ`, with
multiplicity: the values `x i` that are non-zero, collected over all `i`. -/
noncomputable def nonzeroEntries (x : ι → ℝ) : Multiset ℝ :=
  ((Finset.univ : Finset ι).val.map x).filter (· ≠ 0)

/-- **Identical non-zero entries.** Two finitely-indexed real families `x : ι → ℝ` and `y : κ → ℝ`
(over possibly different index types) have the *same non-zero entries* when the multiset of non-zero
values of `x` equals that of `y`. This is Nielsen and Chuang's `≅` on vectors: equality up to a
permutation of the entries and the insertion/deletion of zeros. -/
def SameNonzero (x : ι → ℝ) (y : κ → ℝ) : Prop :=
  nonzeroEntries x = nonzeroEntries y
