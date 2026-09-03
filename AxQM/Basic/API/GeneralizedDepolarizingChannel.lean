/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumChannel
import AxQM.Basic.API.MaximallyMixed
import AxQM.Basic.API.Qudit
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl

/-!
# AxQM.Basic.API — the generalized depolarizing channel and its operator sum

The **generalized depolarizing channel** on a `d`-dimensional quantum system (Nielsen & Chuang,
§8.3.4, eq. 8.106): with probability `p` the state is replaced by the maximally mixed state `I/d`,
and left untouched otherwise,
`E(ρ) = p (I/d) + (1 - p) ρ`.
This file gives its **operator-sum (Kraus) representation** — the object Nielsen & Chuang,
Exercise 8.19 asks for.
-/

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **computational orthonormal basis** `{|i⟩}` of `qudit d` (the standard basis of
`EuclideanSpace ℂ (Fin d)`). -/
def quditOrthonormalBasis (d : ℕ) : OrthonormalBasis (Fin d) ℂ (qudit d).space :=
  EuclideanSpace.basisFun (Fin d) ℂ

/-- The `j`-th **depolarizing-design unitary** of the computational basis of `qudit d`, as a
(unitary) operator on the qudit space. Ranging over `j : (Fin d → Bool) × Equiv.Perm (Fin d)` these
are the `2ᵈ d!` sign-flip×permutation unitaries. -/
def depolarizingOp (d : ℕ) (j : (Fin d → Bool) × Equiv.Perm (Fin d)) :
    (qudit d).space →L[ℂ] (qudit d).space :=
  ((quditOrthonormalBasis d).depolarizingUnitary j).toContinuousLinearEquiv

/-- **The generalized depolarizing channel** `E(ρ) = (1 - p) ρ + p (I/d)` on `qudit d` (Nielsen &
Chuang eq. 8.106): with probability `p` the state is replaced by the maximally mixed state `I/d
= maximallyMixedState`, and left untouched otherwise. -/
def genDepolarizingChannel (d : ℕ) [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) : State (qudit d) where
  op := ((1 - p : ℝ) : ℂ) • ρ.op + ((p : ℝ) : ℂ) • (maximallyMixedState (qudit d)).op
  isDensity :=
    ContinuousLinearMap.IsDensityOp.convex_combination ρ.isDensity
      (maximallyMixedState (qudit d)).isDensity
      (by exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - p)) (by exact_mod_cast hp0)
      (by push_cast; ring)

/-- The **operation elements** of the generalized depolarizing channel, indexed by
`Option ((Fin d → Bool) × Equiv.Perm (Fin d))`:

* `none ↦ √(1-p) · I` — the "leave `ρ` untouched" branch;
* `some j ↦ √(p / 2ᵈd!) · Uⱼ` — one element per depolarizing-design unitary `Uⱼ`
  (`depolarizingOp`). -/
def genDepolarizingKraus (d : ℕ) (p : ℝ) :
    Option ((Fin d → Bool) × Equiv.Perm (Fin d)) →
      ((qudit d).space →L[ℂ] (qudit d).space)
  | none => (Real.sqrt (1 - p) : ℂ) • 1
  | some j => (Real.sqrt (p / (2 ^ d * d.factorial : ℝ)) : ℂ) • depolarizingOp d j

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the generalized-depolarizing operation
elements (Nielsen & Chuang's trace condition, certifying `E` is trace preserving). -/
theorem genDepolarizingKraus_completeness [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ k, (adjoint (genDepolarizingKraus d p k)).comp (genDepolarizingKraus d p k) = 1 := sorry

/-- **The operator-sum (Kraus) representation of the generalized depolarizing channel** (Nielsen &
Chuang, Exercise 8.19): the channel acts as the operator sum of its operation elements, `E(ρ) =
∑ₖ Eₖ ρ Eₖ†`. -/
theorem genDepolarizingChannel_op_eq_krausSum [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) :
    (genDepolarizingChannel d p hp0 hp1 ρ).op = krausSumₗ (genDepolarizingKraus d p) ρ.op := sorry

end AxQM
