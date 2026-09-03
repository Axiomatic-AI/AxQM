/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import AxQM.ToMathlib.Analysis.Convex.Majorization

/-!
# Majorization of Hermitian matrices

For Hermitian matrices `H`, `K` over an `RCLike` field, Nielsen and Chuang write `H ≺ K` to mean
that the vector of eigenvalues of `H` is majorized by that of `K`, `λ(H) ≺ λ(K)` (`Majorize`).
This file records that relation as `Matrix.IsHermitian.Majorize` and states the operator
majorization theorem (Nielsen–Chuang, *Quantum Computation and Quantum Information*,
Theorem 12.13).

## Main definitions

* `Matrix.IsHermitian.Majorize hH hK`: the eigenvalues of `H` are majorized by those of `K`.

## Main statements

* `Matrix.IsHermitian.majorize_iff_exists_sum_smul_unitary_conj`: Theorem 12.13 itself, the
  biconditional `H ≺ K ↔ H = ∑ⱼ pⱼ Uⱼ K Uⱼ†`.

## Tags

majorization, Hermitian matrix, doubly stochastic, unitary
-/

public section

open Finset Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

namespace IsHermitian

variable {H K : Matrix n n 𝕜}

/-- Majorization of Hermitian matrices (Nielsen–Chuang §12.5): `hH.Majorize hK` means the vector of
eigenvalues of `H` is majorized by that of `K`.  Written `H ≺ K` in Nielsen and Chuang. -/
def Majorize (hH : H.IsHermitian) (hK : K.IsHermitian) : Prop :=
  _root_.Majorize hH.eigenvalues hK.eigenvalues

/-- **Nielsen–Chuang Theorem 12.13** (Uhlmann's operator majorization theorem): for Hermitian
matrices `H`, `K`, the eigenvalues of `H` are majorized by those of `K` (`H ≺ K`) if and only if
`H` is a probabilistic mixture of unitary conjugates of `K`, `H = ∑ⱼ pⱼ Uⱼ K Uⱼ†` for some
probability distribution `pⱼ` and unitaries `Uⱼ`. -/
theorem majorize_iff_exists_sum_smul_unitary_conj (hH : H.IsHermitian) (hK : K.IsHermitian) :
    hH.Majorize hK ↔
      ∃ (m : ℕ) (p : Fin m → ℝ) (U : Fin m → Matrix n n 𝕜),
        (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧ (∀ j, U j ∈ unitaryGroup n 𝕜) ∧
          H = ∑ j, p j • (U j * K * (U j)ᴴ) := sorry

end IsHermitian

end Matrix
