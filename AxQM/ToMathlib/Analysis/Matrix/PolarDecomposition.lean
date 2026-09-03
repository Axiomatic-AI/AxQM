/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# Polar decomposition of positive, unitary and Hermitian matrices

The *polar decomposition* of a square matrix `A` writes `A = U * J` (and `A = K * U`) with `U`
unitary and `J`, `K` positive semidefinite, where the positive factors are the canonical
`J = √(Aᴴ * A)` and `K = √(A * Aᴴ)` (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 2.3). Here `√` is the positive semidefinite square root `CFC.sqrt` supplied by
the continuous functional calculus on the C⋆-algebra `Matrix n n 𝕜`, whose scoped `MatrixOrder`
instances make `Matrix n n 𝕜` a `StarOrderedRing` and identify `0 ≤ A` with `A.PosSemidef`.

## Main results

* `Matrix.PosSemidef.sqrt_conjTranspose_mul_self`,
  `Matrix.PosSemidef.sqrt_mul_conjTranspose_self`: for a positive semidefinite `P`, both polar
  factors are `P` itself, `√(Pᴴ * P) = √(P * Pᴴ) = P`.
* `Matrix.PosSemidef.eq_one_mul_sqrt_conjTranspose_mul_self`: the polar decomposition of a positive
  semidefinite matrix, `P = 1 * √(Pᴴ * P)` (unitary factor `1`).
* `Matrix.sqrt_conjTranspose_mul_self_of_mem_unitaryGroup`,
  `Matrix.sqrt_mul_conjTranspose_self_of_mem_unitaryGroup`: for a unitary `U`, both polar factors
  are the identity, `√(Uᴴ * U) = √(U * Uᴴ) = 1`.
* `Matrix.eq_mul_sqrt_conjTranspose_mul_self_of_mem_unitaryGroup`: the polar decomposition of a
  unitary matrix, `U = U * √(Uᴴ * U)` (positive factor `1`).
* `Matrix.IsHermitian.sqrt_conjTranspose_mul_self`: for a Hermitian `H`, the positive factor is the
  *absolute value* `√(H ^ 2)` (i.e. `|H|`), `√(Hᴴ * H) = √(H ^ 2)`.
* `Matrix.IsHermitian.polarUnitary`, `Matrix.IsHermitian.polarUnitary_mem_unitaryGroup` and
  `Matrix.IsHermitian.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self`: the unitary factor of a
  Hermitian `H` is its *sign* `sgn(H)`, giving the decomposition `H = sgn(H) · |H|`.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

set_option linter.unusedDecidableInType false in
/-- **N&C Exercise 2.48, positive case (left factor).** The positive factor `√(Pᴴ * P)` of the
polar decomposition of a positive semidefinite matrix `P` is `P` itself. -/
theorem PosSemidef.sqrt_conjTranspose_mul_self {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    CFC.sqrt (Pᴴ * P) = P := sorry

set_option linter.unusedDecidableInType false in
/-- **N&C Exercise 2.48, positive case (right factor).** The positive factor `√(P * Pᴴ)` of the
polar decomposition of a positive semidefinite matrix `P` is `P` itself. -/
theorem PosSemidef.sqrt_mul_conjTranspose_self {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    CFC.sqrt (P * Pᴴ) = P := sorry

/-- **N&C Exercise 2.48, positive case (decomposition).** The polar decomposition of a positive
semidefinite matrix `P` is `P = I · P`: the unitary factor is `1` and the positive factor is `P`
(`= √(Pᴴ * P)`). -/
theorem PosSemidef.eq_one_mul_sqrt_conjTranspose_mul_self {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    P = 1 * CFC.sqrt (Pᴴ * P) := sorry

/-- **N&C Exercise 2.48, unitary case (left factor).** The positive factor `√(Uᴴ * U)` of the polar
decomposition of a unitary matrix `U` is the identity. -/
theorem sqrt_conjTranspose_mul_self_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : CFC.sqrt (Uᴴ * U) = 1 := sorry

/-- **N&C Exercise 2.48, unitary case (right factor).** The positive factor `√(U * Uᴴ)` of the polar
decomposition of a unitary matrix `U` is the identity. -/
theorem sqrt_mul_conjTranspose_self_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : CFC.sqrt (U * Uᴴ) = 1 := sorry

/-- **N&C Exercise 2.48, unitary case (decomposition).** The polar decomposition of a unitary matrix
`U` is `U = U · I`: the unitary factor is `U` and the positive factor is `1` (`= √(Uᴴ * U)`). -/
theorem eq_mul_sqrt_conjTranspose_mul_self_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : U = U * CFC.sqrt (Uᴴ * U) := sorry

/-- **N&C Exercise 2.48, Hermitian case.** The positive factor `√(Hᴴ * H)` of the polar
decomposition of a Hermitian matrix `H` is its absolute value `|H| = √(H ^ 2)`. -/
theorem IsHermitian.sqrt_conjTranspose_mul_self {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    CFC.sqrt (Hᴴ * H) = CFC.sqrt (H ^ 2) := sorry

/-- The real sign function normalised to take the value `1` at `0` (rather than the usual `0`), so
that `polarSign x * |x| = x` while `polarSign x` is always a unit. -/
noncomputable def polarSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- The unitary factor of the polar decomposition of a Hermitian matrix `H`. -/
noncomputable def IsHermitian.polarUnitary {H : Matrix n n 𝕜} (_hH : H.IsHermitian) :
    Matrix n n 𝕜 := cfc polarSign H

/-- **N&C Exercise 2.48, Hermitian case (unitary factor).** The sign factor `sgn(H)` of the polar
decomposition of a Hermitian matrix is unitary. -/
theorem IsHermitian.polarUnitary_mem_unitaryGroup {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    hH.polarUnitary ∈ unitaryGroup n 𝕜 := sorry

/-- **N&C Exercise 2.48, Hermitian case (decomposition).** A Hermitian matrix `H` factors as `H =
sgn(H) · |H|`. -/
theorem IsHermitian.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) : H = hH.polarUnitary * CFC.sqrt (Hᴴ * H) := sorry

end Matrix
