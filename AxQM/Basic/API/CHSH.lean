/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Observable
import AxQM.Basic.API.Qubit
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Algebra.Star.CHSH

/-!
# AxQM.Basic.API — CHSH operators of a bipartite system (Tsirelson)

The **CHSH operators** on a composite system `S ⊗ T`, built from a pair of observables on each
factor. This is the operator-level core of Nielsen & Chuang **Problem 2.3** (Tsirelson's
inequality).
-/

open scoped InnerProductSpace TensorProduct ComplexOrder

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Nielsen & Chuang (2.233), tensor form.** For involutive observables `A₀, A₁` on `S` and
`B₀, B₁` on `T`, the square of the CHSH operator is
`(A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ - A₁⊗B₁)² = 4 + ⁅A₁,A₀⁆ ⊗ ⁅B₀,B₁⁆`, where the scalar `4` is the
`4·(identity)` of the operator algebra — the `4I` of the textbook.
-/
theorem chsh_tmul_sq (A₀ A₁ : Observable S) (B₀ B₁ : Observable T)
    (hA₀ : A₀.op * A₀.op = 1) (hA₁ : A₁.op * A₁.op = 1)
    (hB₀ : B₀.op * B₀.op = 1) (hB₁ : B₁.op * B₁.op = 1) :
    ((A₀ ⊗ B₀).op + (A₀ ⊗ B₁).op + (A₁ ⊗ B₀).op - (A₁ ⊗ B₁).op) ^ 2
      = 4 • (1 : (S ⊗ T) →L[ℂ] (S ⊗ T)) + TensorProduct.mapL ⁅A₁.op, A₀.op⁆ ⁅B₀.op, B₁.op⁆ := sorry

end AxQM
