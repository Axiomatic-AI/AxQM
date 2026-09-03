/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.HadamardEigen

/-!
# AxQM.Basic.API — the eigenprojectors of `v · σ` project onto its `±1` eigenspaces

The **second half of Nielsen & Chuang Exercise 2.60** (§2.2.5, p. 90): the eigenspace projectors
of `v⃗·σ⃗` are `P± = (I ± v⃗·σ⃗)/2`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

open ContinuousLinearMap Matrix

variable {S : QSystem}

/-- **`P₊` projects into the `+1` eigenspace:** `A · P₊ = P₊`, so `A(P₊ w) = P₊ w` for every `w`. -/
theorem Observable.op_mul_projPlus (A : Observable S) (hinv : A.op * A.op = 1) :
    A.op * A.projPlus = A.projPlus := sorry

/-- **`P₋` projects into the `−1` eigenspace:** `A · P₋ = −P₋`, so `A(P₋ w) = −(P₋ w)` for every
`w`. -/
theorem Observable.op_mul_projMinus (A : Observable S) (hinv : A.op * A.op = 1) :
    A.op * A.projMinus = -A.projMinus := sorry

/-- **The `+1` eigenspace lies in the range of `P₊`:** if `A u = u` then `P₊ u = u`. -/
theorem Observable.projPlus_apply_eq_self (A : Observable S) {u : S.space} (hu : A.op u = u) :
    A.projPlus u = u := sorry

/-- **The `−1` eigenspace lies in the range of `P₋`:** if `A u = −u` then `P₋ u = u`. -/
theorem Observable.projMinus_apply_eq_self (A : Observable S) {u : S.space} (hu : A.op u = -u) :
    A.projMinus u = u := sorry

/-- **`P₊` on a `c`-eigenvector:** if `A u = c • u` then `P₊ u = ½(1 + c) • u`, the
`+1`-measurement coefficient on any eigenvector of a `±1` observable. -/
theorem Observable.projPlus_apply_smul (A : Observable S) {v : S.space} {c : ℂ}
    (h : A.op v = c • v) : A.projPlus v = (2⁻¹ * (1 + c)) • v := by
  rw [Observable.projPlus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, h]
  module

/-- **`P₋` on a `c`-eigenvector:** if `A u = c • u` then `P₋ u = ½(1 − c) • u`, the
`−1`-measurement coefficient on any eigenvector of a `±1` observable. -/
theorem Observable.projMinus_apply_smul (A : Observable S) {v : S.space} {c : ℂ}
    (h : A.op v = c • v) : A.projMinus v = (2⁻¹ * (1 - c)) • v := by
  rw [Observable.projMinus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, h]
  module

end AxQM
