/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.ParityCheck
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Reducing a parity-check matrix to standard form `[A ∣ I]`

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1, the second
half of **Exercise 10.16** (p. 447): row reduction and a reordering of the bits let one assume the
parity-check matrix has the standard form `[A ∣ I_{n−k}]`, with `A` of size `(n − k) × k`.

## Main results

* `LinearCode.exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective`: **the standard form**
  (Exercise 10.16, second claim). For a full-row-rank `H` there is an invertible row operation `E`
  and a choice of `n − k` coordinates `f` such that `E * H` has the identity on those coordinates,
  `(E * H).submatrix id f = 1`, and still checks the same code, `ofParityCheck (E * H) =
  ofParityCheck H`. Reordering the coordinates so that `f` lands last exhibits `E * H = [A ∣ I]`.
-/

open Matrix

@[expose] public section

namespace LinearCode

variable {K : Type*} [Field K] {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]

/-- **Standard form of a parity-check matrix** (Nielsen & Chuang, Exercise 10.16, p. 447, second
claim). Reordering the coordinates so that `f` comes last displays `E * H = [A ∣ I_{n−k}]`,
where the off-`f` columns form `A`. -/
theorem exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective
    (H : Matrix μ ι K) (hH : Function.Surjective H.mulVecLin) :
    ∃ E : Matrix μ μ K, IsUnit E ∧ ∃ f : μ → ι, Function.Injective f ∧
      (E * H).submatrix id f = 1 ∧ ofParityCheck (E * H) = ofParityCheck H := sorry

end LinearCode

end
