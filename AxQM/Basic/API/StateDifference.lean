/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# AxQM — the positive/negative decomposition of a state difference (N&C Ex 9.7)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 9.7 (p. 405): the
difference of two density operators splits into positive and negative parts supported on
orthogonal subspaces.

## Main statements

* `State.exists_isPositive_sub_op_sub` — N&C Exercise 9.7: for any states `ρ σ`, there exist
  positive operators `Q R` with `ρ.op − σ.op = Q − R`, `Q * R = 0`, and `range Q ⟂ range R`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.7.** For any states `ρ` and `σ` of the system `S`, the
difference of their density operators decomposes as `ρ.op − σ.op = Q − R` with `Q` and `R`
positive operators supported on orthogonal subspaces: `Q * R = 0` and `range Q ⟂ range R`.
-/
theorem State.exists_isPositive_sub_op_sub (ρ σ : State S) :
    ∃ Q R : S →L[ℂ] S, Q.IsPositive ∧ R.IsPositive ∧ ρ.op - σ.op = Q - R ∧ Q * R = 0 ∧
      LinearMap.range (Q : S →ₗ[ℂ] S) ⟂ LinearMap.range (R : S →ₗ[ℂ] S) := sorry

end AxQM
