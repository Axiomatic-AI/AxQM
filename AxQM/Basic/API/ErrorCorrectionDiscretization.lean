/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumChannel

/-!
# AxQM.Basic.API — discretization of the errors (Nielsen & Chuang, Theorem 10.2)

Nielsen & Chuang's **Theorem 10.2** (the *discretization of the errors*, p. 438) is the deep fact
that makes quantum error-correction possible: a recovery operation built to correct one noise
process automatically corrects a whole *continuum* of noise processes.

## Contents

* `AxQM.CorrectsErrors` — the clean correction criterion `∃ c, ∀ k i, Rₖ Eᵢ P = cₖᵢ P`
  for a code projector `P`, recovery elements `R`, and error elements `E`.
* `AxQM.correctsErrors_krausSumₗ_op_proportional_linearCombination` — Theorem 10.2 in
  full: `∃ λ ≥ 0, ∀ ρ ⊆ C, (R ∘ F)(ρ) = λ ρ` for the linear-combination noise `F`.
-/

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A recovery family corrects a set of errors on a code** (Nielsen & Chuang, the clean correction
criterion of Theorem 10.1, Eqs. (10.29) and (10.35)). Given a code projector `P : S.space →L[ℂ]
S.space`, recovery operation elements `R : κ → S.space →L[ℂ] S.space`, and error operation
elements `E : ι → S.space →L[ℂ] S.space`, we say `R` **corrects** `E` on the code `P` when there
are scalars `cₖᵢ` with

`Rₖ Eᵢ P = cₖᵢ P`   for all `k, i`

Physically: after an error `Eᵢ` acts on a code state and recovery Kraus element `Rₖ` is applied,
the result is the code state back again up to the scalar `cₖᵢ`.
-/
def CorrectsErrors {κ ι : Type*} (P : S.space →L[ℂ] S.space)
    (R : κ → S.space →L[ℂ] S.space) (E : ι → S.space →L[ℂ] S.space) : Prop :=
  ∃ c : κ → ι → ℂ, ∀ (k : κ) (i : ι), R k * E i * P = c k i • P

/-- **Theorem 10.2 (discretization of the errors), in full** (Nielsen & Chuang, p. 438).

`∀ ρ ⊆ C,  (R ∘ F)(ρ) = λ ρ`,

i.e. `R ∘ F` is proportional to the identity channel on the whole code — N&C's `R(F(ρ)) ∝ ρ`
with a uniform constant (Eq. (10.39)).
-/
theorem correctsErrors_krausSumₗ_op_proportional_linearCombination {κ ι ι' : Type*}
    [Fintype κ] [Fintype ι] [Fintype ι'] {P : S.space →L[ℂ] S.space}
    {R : κ → S.space →L[ℂ] S.space} {E : ι → S.space →L[ℂ] S.space} (m : ι' → ι → ℂ)
    (h : CorrectsErrors P R E) (hP : IsSelfAdjoint P) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ ρ : State S, P * ρ.op * P = ρ.op →
      ContinuousLinearMap.krausSumₗ R
          (ContinuousLinearMap.krausSumₗ (fun j => ∑ i, m j i • E i) ρ.op)
        = (lam : ℂ) • ρ.op := sorry

end AxQM
