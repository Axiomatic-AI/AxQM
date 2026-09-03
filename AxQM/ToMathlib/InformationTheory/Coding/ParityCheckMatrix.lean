/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Consistency of generator and parity-check matrices: `H * G = 0`

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1, a linear code
has two equivalent presentations, by a generator matrix `G` and by a parity-check matrix `H`.

## Main results

* `Matrix.mul_eq_zero_of_range_mulVecLin_eq_ker`: **Exercise 10.18** — when `H` and `G` present the
  *same* code (`range G.mulVecLin = ker H.mulVecLin`), `H * G = 0`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommSemiring R] {l m n : Type*} [Fintype m] [Fintype n]

/-- **Nielsen & Chuang, Exercise 10.18** (p. 447): the parity-check matrix `H` and generator matrix
`G` for the same linear code satisfy `H * G = 0`. -/
theorem mul_eq_zero_of_range_mulVecLin_eq_ker (H : Matrix l m R) (G : Matrix m n R)
    (h : LinearMap.range G.mulVecLin = LinearMap.ker H.mulVecLin) :
    H * G = 0 := sorry

end Matrix
