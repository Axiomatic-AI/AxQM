/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linear codes and their minimum distance

A **linear code** of block length `ι` over a field `K` is a `K`-subspace of the word space
`ι → K` (Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1). Its codewords
are the elements of the subspace, and its error-correcting power is measured by the *minimum
distance*: the least Hamming weight of a nonzero codeword.

## Main definitions

* `LinearCode K ι`: a linear code, i.e. a `Submodule K (ι → K)`.
* `LinearCode.minDist C`: the minimum distance `d(C)`, the least Hamming weight of a nonzero
  codeword (N&C eq. (10.61)), valued in `ℕ∞` (with `⊤` for the trivial code `{0}`).
* `LinearCode.CorrectsErrors C t`: `C` *corrects `t` errors*, meaning `d(C) ≥ 2t + 1` (N&C p. 448).
-/

@[expose] public section

/-- A **linear code** of block length `ι` over a field `K`: a `K`-subspace of the word space `ι →
K`, whose elements are the codewords (Nielsen & Chuang, §10.4.1). -/
abbrev LinearCode (K ι : Type*) [Field K] : Type _ := Submodule K (ι → K)

namespace LinearCode

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K]

/-- The **minimum distance** `d(C)` of a linear code: the least Hamming weight of a nonzero
codeword (Nielsen & Chuang, eq. (10.61)), valued in `ℕ∞`. The trivial code `{0}`, having no nonzero
codeword, has minimum distance `⊤`. -/
noncomputable def minDist (C : LinearCode K ι) : ℕ∞ :=
  ⨅ c ∈ {c : ι → K | c ∈ C ∧ c ≠ 0}, (hammingNorm c : ℕ∞)

/-- A linear code **corrects `t` errors** when its minimum distance is at least `2t + 1`
(Nielsen & Chuang, p. 448): decoding a corrupted word to the nearest codeword recovers from up to
`t` symbol errors. -/
def CorrectsErrors (C : LinearCode K ι) (t : ℕ) : Prop := (↑(2 * t + 1) : ℕ∞) ≤ minDist C

end LinearCode
