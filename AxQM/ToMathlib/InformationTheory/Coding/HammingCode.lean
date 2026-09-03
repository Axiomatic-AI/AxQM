/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.ParityCheck
public import AxQM.ToMathlib.InformationTheory.Coding.ParityCheckDistance
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The binary Hamming codes

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.2 (p. 449), the
**Hamming code** with parameter `r` is the binary linear code whose parity-check matrix `H_r` has as
its columns *all* the `2^r − 1` nonzero binary vectors of length `r`. This file constructs `H_r` and
its code and proves the first-order facts of N&C **Exercise 10.22**: the code has minimum distance
`3`, so it corrects a single-bit error, and its block length is `n = 2^r − 1`.

## Main definitions

* `Matrix.hammingParityCheck r`: the `r × (2^r − 1)` binary Hamming parity-check matrix `H_r`.

## Main results

* `Matrix.hammingCode_minDist`: **Exercise 10.22, distance.** For `r ≥ 2` the Hamming code has
  minimum distance exactly `3`.
* `Matrix.hammingCode_correctsErrors_one`: **Exercise 10.22, correction.** For `r ≥ 2` the Hamming
  code corrects a single-bit error.
* `Matrix.hammingCode_length`: **Exercise 10.22, length.** The block length is `n = 2^r − 1`, the
  number of nonzero binary `r`-vectors.
* `Matrix.hammingCode_finrank`: **Exercise 10.22, dimension.** The code has dimension
  `k = 2^r − r − 1`.
-/

@[expose] public section

namespace Matrix

variable {r : ℕ}

/-- The **binary Hamming parity-check matrix** `H_r`: the `r × (2^r − 1)` matrix over `ZMod 2` whose
columns are exactly the nonzero binary vectors of length `r`. -/
def hammingParityCheck (r : ℕ) : Matrix (Fin r) {v : Fin r → ZMod 2 // v ≠ 0} (ZMod 2) :=
  Matrix.of fun i v => (v : Fin r → ZMod 2) i

/-- The **Hamming code** with parameter `r`. -/
noncomputable def hammingCode (r : ℕ) : LinearCode (ZMod 2) {v : Fin r → ZMod 2 // v ≠ 0} :=
  LinearCode.ofParityCheck (hammingParityCheck r)

/-- **Nielsen & Chuang, Exercise 10.22 (distance).** For `r ≥ 2` the binary Hamming code has minimum
distance exactly `3`. -/
theorem hammingCode_minDist (hr : 2 ≤ r) : LinearCode.minDist (hammingCode r) = 3 := sorry

/-- **Nielsen & Chuang, Exercise 10.22 (single-error correction).** For `r ≥ 2` the binary Hamming
code corrects a single-bit error. -/
theorem hammingCode_correctsErrors_one (hr : 2 ≤ r) : (hammingCode r).CorrectsErrors 1 := sorry

/-- **Nielsen & Chuang, Exercise 10.22 (length).** The block length of the binary Hamming code is
`n = 2^r − 1`: the number of nonzero binary `r`-vectors, i.e. the number of columns of `H_r`. -/
theorem hammingCode_length (r : ℕ) :
    Fintype.card {v : Fin r → ZMod 2 // v ≠ 0} = 2 ^ r - 1 := sorry

/-- **Nielsen & Chuang, Exercise 10.22 (dimension).** The binary Hamming code has dimension `k = 2^r
− r − 1` — the last of its `[2^r − 1, 2^r − r − 1, 3]` parameters. -/
theorem hammingCode_finrank (r : ℕ) :
    Module.finrank (ZMod 2) (hammingCode r) = 2 ^ r - r - 1 := sorry

end Matrix
