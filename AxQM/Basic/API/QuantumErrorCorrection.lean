/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumErrorCorrection

/-!
# AxQM.Basic.API — quantum error-correction conditions (N&C, Theorem 10.1)

Nielsen & Chuang's **Theorem 10.1** (the *quantum error-correction conditions*, p. 436)
characterises when a noise process can be reversed on a code.

## Contents

* `AxQM.SatisfiesQECConditions` — the **quantum error-correction conditions** as a
  predicate on a code projector `P` and noise operation elements `E`:
  `∃ Hermitian α, P Eᵢ† Eⱼ P = αᵢⱼ P` (N&C Eq. (10.16)).
* `AxQM.satisfiesQECConditions_iff_exists_correction` — **Theorem 10.1**, as the
  biconditional: `SatisfiesQECConditions P E ↔` there exists a trace-preserving recovery family
  `R` (`∑ₒ Rₒ† Rₒ = 1`) correcting `E` on the code.
-/

open scoped Matrix

noncomputable section

namespace AxQM

universe uι

variable {S : QSystem} {ι : Type uι} [Fintype ι]

/-- **The quantum error-correction conditions** (Nielsen & Chuang, Theorem 10.1, Eq. (10.16)), as a
predicate on a quantum system `S`: for some Hermitian matrix `α`, `P Eᵢ† Eⱼ P = αᵢⱼ P`. -/
def SatisfiesQECConditions (P : S.space →L[ℂ] S.space) (E : ι → S.space →L[ℂ] S.space) : Prop :=
  ∃ α : Matrix ι ι ℂ, α.IsHermitian ∧ ContinuousLinearMap.SatisfiesKLConditions P E α

/-- **Nielsen & Chuang, Theorem 10.1, for a quantum system.** For a **nonzero** orthogonal code
projector `P` (self-adjoint idempotent) on a quantum system `S` and a finite family of noise
operation elements `E`, the quantum error-correction conditions hold **iff** there is a
**trace-preserving** recovery family `R` (`∑ₒ Rₒ† Rₒ = 1` — an error-correction operation) that
**corrects** `E` on the code (`ContinuousLinearMap.Corrects P E R`: the composed
noise-then-recovery operator sum returns every operator supported on the code to a scalar
multiple of itself).

No assumption is made that `E` is itself a valid quantum operation (`∑ᵢ Eᵢ† Eᵢ ≤ 1`).
-/
theorem satisfiesQECConditions_iff_exists_correction {P : S.space →L[ℂ] S.space}
    {E : ι → S.space →L[ℂ] S.space}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0) :
    SatisfiesQECConditions P E ↔
      ∃ (κ : Type uι) (_ : Fintype κ) (R : κ → S.space →L[ℂ] S.space),
        (∑ o, ContinuousLinearMap.adjoint (R o) ∘L R o = 1) ∧
          ContinuousLinearMap.Corrects P E R := sorry

end AxQM
