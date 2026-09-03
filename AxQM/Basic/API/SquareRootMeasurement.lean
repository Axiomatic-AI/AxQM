/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The square-root measurement realising a POVM (the `POVM → Measurement` bridge)

The primitive `Measurement ι S` stores *measurement operators* `Mᵢ` together with the
completeness relation `∑ᵢ Mᵢ† Mᵢ = 1`; its induced POVM `toPOVM` has effects `Eᵢ = Mᵢ† Mᵢ`
(`Measurement.toPOVM`).  Going the other way — realising a *given* POVM `{Eᵢ}` (positive effects
summing to `1`) as an actual measurement — requires choosing measurement operators `Mᵢ` with
`Mᵢ† Mᵢ = Eᵢ`.  The **canonical** such choice is `Mᵢ = √Eᵢ`, the operator square root
(`cfc Real.sqrt Eᵢ`): this is the **square-root (or "pretty-good") measurement** of `{Eᵢ}`.

## Main declarations
* `AxQM.Measurement.ofPOVM` — the square-root measurement `Mᵢ = √Eᵢ` of a POVM `P`.
* `AxQM.Measurement.ofPOVM_op` — its operators, `(ofPOVM P).op i = √(P.elements i)`.
* `AxQM.Measurement.toPOVM_ofPOVM` — the round-trip `(ofPOVM P).toPOVM = P`: the
  square-root measurement induces exactly the POVM it was built from.
* `AxQM.Measurement.ofPOVM_bornProb` — its Born rule is the POVM Born rule,
  `p(i) = P.toPMF ρ`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The operator square root squares back through the adjoint**: for a positive operator `A ≥ 0`
on a complex Hilbert space, `(√A)† √A = A`, where `√A = cfc Real.sqrt A`. -/
private theorem cfc_real_sqrt_adjoint_comp_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    (ContinuousLinearMap.adjoint (cfc Real.sqrt A)).comp (cfc Real.sqrt A) = A := by
  rw [ContinuousLinearMap.adjoint_cfc_real_sqrt, ← ContinuousLinearMap.mul_def,
    cfc_real_sqrt_mul_self_of_nonneg hA]

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **The square-root ("pretty-good") measurement realising a POVM** `P` on the system `S`: the
measurement whose operators are the operator square roots of the POVM's effects, `Mᵢ = √Eᵢ = cfc
Real.sqrt (P.elements i)`. This is the canonical partial inverse of `Measurement.toPOVM`, turning
a family of positive effects back into a `Measurement`. -/
def Measurement.ofPOVM (P : POVM ι ℂ S.space) : Measurement ι S where
  op i := cfc Real.sqrt (P.elements i)
  complete :=
    calc ∑ i, (ContinuousLinearMap.adjoint (cfc Real.sqrt (P.elements i))).comp
            (cfc Real.sqrt (P.elements i))
        = ∑ i, P.elements i :=
          Finset.sum_congr rfl fun i _ =>
            cfc_real_sqrt_adjoint_comp_self
              ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (P.isPositive i))
      _ = 1 := P.sum_eq_one

@[simp]
theorem Measurement.ofPOVM_op (P : POVM ι ℂ S.space) (i : ι) :
    (Measurement.ofPOVM P).op i = cfc Real.sqrt (P.elements i) := rfl

/-- **Round-trip**: the square-root measurement of a POVM induces exactly that POVM, `(ofPOVM
P).toPOVM = P`. Thus `Measurement.ofPOVM` is a genuine section of `Measurement.toPOVM`. -/
@[simp]
theorem Measurement.toPOVM_ofPOVM (P : POVM ι ℂ S.space) :
    (Measurement.ofPOVM P).toPOVM = P := by
  refine POVM.ext (funext fun i => ?_)
  rw [Measurement.toPOVM_elements, Measurement.ofPOVM_op]
  exact cfc_real_sqrt_adjoint_comp_self
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (P.isPositive i))

/-- **Born rule of the square-root measurement**: measuring `ofPOVM P` on a state `ρ` gives outcome
`i` with the POVM's own Born probability, `(ofPOVM P).bornProb ρ i = P.toPMF ρ`. -/
theorem Measurement.ofPOVM_bornProb (P : POVM ι ℂ S.space) (ρ : State S) (i : ι) :
    (Measurement.ofPOVM P).bornProb ρ i = P.toPMF ρ.op i := by
  rw [Measurement.bornProb, Measurement.toPOVM_ofPOVM]

end AxQM
