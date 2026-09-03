/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The repetition code, its generator matrix, and a parity-check matrix

The **repetition code** encoding `k` symbols by repeating each of them `r` times is the classical
`[rk, k]` linear code of Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise
10.14 (p. 446). This file writes out the generator matrix that N&C's exercise asks for, and proves
that it does encode `k` symbols by `r`-fold repetition and that the resulting code is genuinely
`k`-dimensional. It also constructs a **parity-check matrix** for the code (N&C p. 447, Exercise
10.17): a matrix whose kernel is the code, and whose rows — being linearly independent — make it a
minimal such matrix.

## Main definitions

* `repetitionGenerator K k r`: the `rk × k` generator matrix `G` with `G (j, s) i = 1` iff `i = j`
  (N&C Exercise 10.14). Its `i`-th column is the indicator of the `r` positions holding copies of
  message symbol `i`.
* `repetitionCode K k r`: the repetition code itself, the span of the columns of the generator
  matrix (`LinearMap.range (repetitionGenerator K k r).mulVecLin`), of type
  `LinearCode K (Fin k × Fin r)`.
* `repetitionParityCheck K k m`: a parity-check matrix `H` for the repetition code with `r = m + 1`
  repetitions (N&C p. 447, Exercise 10.17). It is the `k·m × k(m+1)` matrix whose row `(j, s)`
  imposes "position `(j, s)` equals position `(j, s+1)`", i.e. `H (j, s) (j', s')` is `1` if
  `(j', s') = (j, s)`, `-1` if `(j', s') = (j, s+1)`, and `0` otherwise. Over `ZMod 2` this is the
  all-`0`/`1` matrix N&C describe (there `−1 = 1`); over a general field the signed differences are
  needed for the kernel to come out right.

## Main results

* `repetitionGenerator_mulVec`: encoding repeats each symbol — `(G *ᵥ x) (j, s) = x j`, so the
  message `x` is sent to the word that carries `r` copies of every `x j` (N&C eqs. (10.55)–(10.56)).
* `repetitionCode_finrank`: for `r ≥ 1` the code has dimension `k`. Together with the block length
  `#(Fin k × Fin r) = k * r`, this is the `[rk, k]` claim of Exercise 10.14.
* `repetitionParityCheck_ker`: **the parity-check property** — the kernel of `H` is exactly the
  repetition code, `ker (repetitionParityCheck K k m).mulVecLin = repetitionCode K k (m + 1)`. This
  is N&C's description of the code as the kernel of `H` (eq. (10.57)); it is Exercise 10.17.
* `repetitionParityCheck_row_linearIndependent`: `H` has linearly independent rows — N&C's
  requirement (p. 447) that a parity-check matrix have independent rows so that its kernel has the
  correct dimension `k`.
-/

@[expose] public section

open Matrix

/-- The **generator matrix** of the `[rk, k]` repetition code (Nielsen & Chuang, Exercise 10.14).
Its `i`-th column is the indicator of the `r` positions `(i, ·)` that hold copies of message
symbol `i`, so that `G *ᵥ x` repeats each symbol of `x` exactly `r` times. -/
def repetitionGenerator (K : Type*) [Field K] (k r : ℕ) :
    Matrix (Fin k × Fin r) (Fin k) K :=
  Matrix.of fun p i => if i = p.1 then 1 else 0

variable {K : Type*} [Field K] {k r : ℕ}

/-- **Encoding repeats each symbol** (Nielsen & Chuang, eqs. (10.55)–(10.56)): the repetition
generator matrix sends a message `x : Fin k → K` to the word carrying `r` copies of every symbol:
`(G *ᵥ x) (j, s) = x j`. -/
theorem repetitionGenerator_mulVec (x : Fin k → K) :
    repetitionGenerator K k r *ᵥ x = fun p => x p.1 := sorry

/-- The **`[rk, k]` repetition code** (Nielsen & Chuang, Exercise 10.14): the linear code whose
codewords are the span of the columns of `repetitionGenerator K k r`, i.e. the range of the
encoding map `x ↦ G *ᵥ x`. -/
noncomputable def repetitionCode (K : Type*) [Field K] (k r : ℕ) :
    LinearCode K (Fin k × Fin r) :=
  LinearMap.range (repetitionGenerator K k r).mulVecLin

/-- **The repetition code has dimension `k`** (`0 < r`). With the block length
`#(Fin k × Fin r) = k * r`, this is the `[rk, k]` content of Nielsen & Chuang, Exercise 10.14. -/
theorem repetitionCode_finrank (hr : 0 < r) :
    Module.finrank K (repetitionCode K k r) = k := sorry

variable {m : ℕ}

/-- A **parity-check matrix** of the `[k(m+1), k]` repetition code (Nielsen & Chuang, p. 447,
Exercise 10.17). Row `(j, s)` imposes the constraint `x (j, s.castSucc) = x (j, s.succ)`, so that
a word lies in `ker H` exactly when it is constant on each block — i.e. when it is a codeword.
Over `ZMod 2` (where `−1 = 1`) this is the all-`0`/`1` matrix N&C describe. -/
def repetitionParityCheck (K : Type*) [Field K] (k m : ℕ) :
    Matrix (Fin k × Fin m) (Fin k × Fin (m + 1)) K :=
  Matrix.of fun p q =>
    if q.1 = p.1 then (if q.2 = p.2.castSucc then 1 else if q.2 = p.2.succ then -1 else 0)
    else 0

/-- **The parity-check property** (Nielsen & Chuang, p. 447, Exercise 10.17): the kernel of the
parity-check matrix is exactly the repetition code (eq. (10.57)). -/
theorem repetitionParityCheck_ker :
    LinearMap.ker (repetitionParityCheck K k m).mulVecLin = repetitionCode K k (m + 1) := sorry

/-- **The rows of the parity-check matrix are linearly independent** (Nielsen & Chuang, p. 447). -/
theorem repetitionParityCheck_row_linearIndependent :
    LinearIndependent K (repetitionParityCheck K k m).row := sorry

end
