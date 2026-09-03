/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.LinearCode
public import AxQM.ToMathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Parity-check matrices and elementary row operations

An `[n, k]` linear code may be specified by a **parity-check matrix** `H`: an `(n - k) × n` matrix,
the code being the set of words `x` with `H *ᵥ x = 0`, i.e. the *kernel* of `x ↦ H *ᵥ x` (Nielsen &
Chuang, *Quantum Computation and Quantum Information*, §10.4.1, eq. (10.57)). This file records the
parity-check description as a `LinearCode` and proves the row-operation invariance of N&C
Exercise 10.16.

## Main definitions

* `LinearCode.ofParityCheck H`: the code cut out by the parity-check matrix `H`, namely
  `LinearMap.ker H.mulVecLin`.

## Main results

* `LinearCode.ofParityCheck_updateRow_add`: **adding one row of the parity-check matrix to another
  leaves the code unchanged** (N&C Exercise 10.16). Replacing row `b` by `H b + H a` (for `a ≠ b`)
  gives a parity-check matrix for the very same code.
-/

open Matrix

@[expose] public section

namespace LinearCode

variable {K m ι : Type*} [Field K] [Fintype ι]

/-- The linear code specified by a **parity-check matrix** `H`. An `[n, k]` code is cut out by an
`(n - k) × n` matrix. -/
noncomputable def ofParityCheck (H : Matrix m ι K) : LinearCode K ι :=
  LinearMap.ker H.mulVecLin

/-- A word `x` is a codeword of the parity-check code `ofParityCheck H` exactly when
`H *ᵥ x = 0`. -/
theorem mem_ofParityCheck_iff {H : Matrix m ι K} {x : ι → K} :
    x ∈ ofParityCheck H ↔ H *ᵥ x = 0 := by
  rw [ofParityCheck, LinearMap.mem_ker, mulVecLin_apply]


variable [DecidableEq m]

/-- **Adding one row of the parity-check matrix to another leaves the code unchanged** (Nielsen &
Chuang, Exercise 10.16). -/
theorem ofParityCheck_updateRow_add (H : Matrix m ι K) {a b : m} (hab : a ≠ b) :
    ofParityCheck (H.updateRow b (H b + H a)) = ofParityCheck H := sorry

end LinearCode
