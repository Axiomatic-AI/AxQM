/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Exercise12_15
import AxQM.NC.Ch12.Theorem12_10

/-!
# N&C Exercise 12.16 — equality in the error-correction entropy bound

*(N&C p. 571.)*

Show S(rho)-S(rho')+S(rho',R) >= 0 holds with equality when R perfectly corrects E.

* `IsPerfectlyCorrected` — the predicate "`R` perfectly corrects `E` for `ρ`" (entanglement fidelity
  `F(ρ, R ∘ E) = 1`, purification form);
* `vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_eq_zero_of_perfectCorrection` — Exercise
  12.16 proper, the balance `= 0` under perfect correction.
-/

noncomputable section

namespace AxQM

variable {Q C D : QSystem}

/-- **"The recovery `R` perfectly corrects the noise `E` for the input `ρ`"** — the entanglement
fidelity `F(ρ, R ∘ E) = 1`, in purification form.

`((refPurify ρ).dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂ = refPurify ρ`.

This is Schumacher's condition for perfect quantum error-correction: the full state *and its
entanglement with a reference* are recovered. Strictly stronger than that pair: a bit-flip
`X(·)X` on `ρ = I/2` satisfies the pair yet has `F = 0`, so is *not* perfect correction.
-/
def State.IsPerfectlyCorrected (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : Prop :=
  ((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂
    = (State.refPurify ρ).toState

/-- **N&C Exercise 12.16.** When the recovery `R` *perfectly* corrects the noise `E` for the input
`ρ` (`State.IsPerfectlyCorrected`, i.e. entanglement fidelity `F(ρ, R ∘ E) = 1`), the
error-correction entropy bound (12.153) holds with equality:

`S(ρ) − S(ρ') + S(ρ', R) = 0`,

with `ρ' = E(ρ) = ρ.dilatedChannel U₁ ω₁` and `S(ρ', R) = (ρ.dilatedChannel U₁ ω₁).entropyExchange`.
-/
theorem State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_eq_zero_of_perfectCorrection
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) (h : ρ.IsPerfectlyCorrected U₁ ω₁ U₂ ω₂) :
    ρ.vonNeumannEntropy - (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy +
      (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ = 0 := sorry

end AxQM
