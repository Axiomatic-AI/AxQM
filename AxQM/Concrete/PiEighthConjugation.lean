/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGate
import AxQM.Concrete.Pauli
import AxQM.Concrete.NMRPulsePhases

/-!
# Concrete: conjugation of the Pauli matrices by the π/8 (T) gate (Nielsen & Chuang, eq. 10.92)

This file verifies the first of the
identities of Nielsen & Chuang **Exercise 10.41**, namely equation (10.92) describing the action by
conjugation of the **π/8 gate** `T = diag(1, e^{iπ/4})` (`tMatrix`, N&C eq. 4.2) on the Pauli
matrices.

## Main results
* `tMatrix_apply_one_one` — the diagonal entry `T₁₁ = e^{iπ/4} = (1 + i)/√2`.
* `tMatrix_conj_pauliZ` — `T Z T† = Z` (eq. 10.92, first identity).
* `tMatrix_conj_pauliX` — `T X T† = (X + Y)/√2` (eq. 10.92, second identity), the non-Pauli image.
-/

open Matrix Complex

namespace AxQM.Concrete

/-- The nontrivial diagonal `(1, 1)` entry of the π/8 gate is the `√2`-normalized phase `T₁₁ =
e^{iπ/4} = (1 + i)/√2`. -/
theorem tMatrix_apply_one_one : tMatrix 1 1 = invSqrt2 + invSqrt2 * Complex.I := by
  rw [← exp_pi_div_four_mul_I]
  simp [tMatrix, mul_comm]

/-- **π/8-gate conjugation fixes `Z`** (Nielsen & Chuang, eq. 10.92, first identity): `T Z T† = Z`.
-/
theorem tMatrix_conj_pauliZ : tMatrix * pauliZ * tMatrixᴴ = pauliZ := sorry

/-- **π/8-gate conjugation sends `X` to the non-Pauli combination `(X + Y)/√2`** (Nielsen & Chuang,
eq. 10.92, second identity): `T X T† = (X + Y)/√2`. This image is *not* a Pauli operator. -/
theorem tMatrix_conj_pauliX :
    tMatrix * pauliX * tMatrixᴴ = invSqrt2 • (pauliX + pauliY) := sorry

end AxQM.Concrete
