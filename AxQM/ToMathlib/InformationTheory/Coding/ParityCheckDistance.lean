/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Minimum distance from the columns of a parity-check matrix

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1, the code
**defined by a parity-check matrix** `H` is the kernel of the check map `x ↦ H *ᵥ x`
(`LinearMap.ker H.mulVecLin`; N&C eq. (10.57)). Its minimum distance is governed by the linear
dependencies among the columns of `H`.

## Main results

* `Matrix.minDist_ker_eq_of_columns`: **Exercise 10.20** — if every set of fewer than `d` columns
  is independent and some `d` columns are dependent, then `d(C) = d`.
-/

@[expose] public section

namespace Matrix

section Distance

variable {K : Type*} {parity ι : Type*} [Field K] [Fintype ι] [DecidableEq K]

/-- **Nielsen & Chuang, Exercise 10.20** (p. 448). -/
theorem minDist_ker_eq_of_columns (H : Matrix parity ι K) {d : ℕ}
    (hindep : ∀ s : Finset ι, s.card < d → LinearIndepOn K (fun j => Hᵀ j) (↑s : Set ι))
    (hdep : ∃ s : Finset ι, s.card = d ∧ ¬ LinearIndepOn K (fun j => Hᵀ j) (↑s : Set ι)) :
    LinearCode.minDist (LinearMap.ker H.mulVecLin) = (d : ℕ∞) := sorry

end Distance

end Matrix
