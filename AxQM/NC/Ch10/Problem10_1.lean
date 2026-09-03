/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.RandomUnitaryChannel
import AxQM.Basic.API.ProjectiveRecovery

/-!
# Nielsen & Chuang, Problem 10.1 — channel equivalence and error-correction

*(N&C p. 495.)*

Channel equivalence E2=U∘E1∘V is an equivalence relation; turn EC code for E1 into one for E2.

* `ChannelEquiv` — the channel-equivalence relation `∃ U V : Evolution S, ∀ ρ, E₂ ρ = U.evolve (E₁
  (V.evolve ρ))`;
* `channelEquiv_equivalence` — it is an equivalence relation (N&C 10.1(1));
* `Corrects` — a *recovery* `R` corrects a channel `E` on a code `C` (a set of code states) when `R
  (E ρ) = ρ` for every `ρ ∈ C`;
* `corrects_of_channelEquiv` — the abstract transfer: from any recovery `R₁` for `E₁` on `C`, the
  recovery `R₂ = V† ∘ R₁ ∘ U†` corrects `E₂` on the transported code `V† C` (this is the content of
  part (2) — a code/recovery for `E₁` becomes one for `E₂`);
* `corrects_conjugate` — the same transfer for a recovery performed in the assumed fashion, "a
  projective measurement followed by a conditional unitary" (a `ProjectiveUnitaryRecovery`):
  the transformed recovery `R.conjugate U V` — new syndrome
  `{U Mᵢ U†}`, new corrections `{V† Wᵢ U†}` — is again a projective measurement followed by a
  conditional unitary, and corrects `E₂`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Channel equivalence** (Nielsen & Chuang, Problem 10.1). Stated on arbitrary state maps (an
equivalence relation regardless of complete positivity). -/
def ChannelEquiv (E₁ E₂ : State S → State S) : Prop :=
  ∃ U V : Evolution S, ∀ ρ : State S, E₂ ρ = U.evolve (E₁ (V.evolve ρ))

/-- **Channel equivalence is an equivalence relation** (Nielsen & Chuang, Problem 10.1(1)).
-/
theorem channelEquiv_equivalence : Equivalence (ChannelEquiv (S := S)) := sorry

/-! ### Part (2): transferring an error-correcting code from `E₁` to `E₂` -/

/-- **A recovery corrects a channel on a code** (Nielsen & Chuang, Problem 10.1(2)). A state map
`R : State S → State S` (the *recovery/error-correction procedure*) **corrects** the channel
`E : State S → State S` on the **code** `C` (the set of encoded/code states) when running the noise
then the recovery returns every code state unchanged: `R (E ρ) = ρ` for all `ρ ∈ C`. This is the
error-correction success condition; the code `C` together with a recovery `R` correcting `E` on it
is precisely "an error-correcting code for `E`". Stated on arbitrary state maps — the condition is a
plain functional identity on the code states, needing no completeness/positivity hypothesis. -/
def Corrects (R E : State S → State S) (C : Set (State S)) : Prop :=
  ∀ ρ ∈ C, R (E ρ) = ρ

/-- **Transferring an error-correcting code along a channel equivalence** (Nielsen & Chuang, Problem
10.1(2)). If `R₁` corrects `E₁` on a code `C`, and `E₂ = U ∘ E₁ ∘ V` is equivalent to `E₁` (the
witnesses `U`, `V` of `ChannelEquiv E₁ E₂`, i.e. `E₂ ρ = U (E₁ (V ρ V†)) U†`), then the recovery
`R₂ = V† ∘ R₁ ∘ U†` corrects `E₂` on the transported code `V† C` (`V.adjoint.evolve '' C`).

This is the abstract heart of part (2): a code/recovery for `E₁` becomes one for `E₂`.
-/
theorem corrects_of_channelEquiv {E₁ E₂ R₁ : State S → State S} {C : Set (State S)}
    (U V : Evolution S) (hE : ∀ ρ, E₂ ρ = U.evolve (E₁ (V.evolve ρ)))
    (hR : Corrects R₁ E₁ C) :
    Corrects (fun σ => V.adjoint.evolve (R₁ (U.adjoint.evolve σ))) E₂ (V.adjoint.evolve '' C) :=
      sorry

/-- **Turning a projective-measurement-then-conditional-unitary recovery for `E₁` into one for
`E₂`** (Nielsen & Chuang, Problem 10.1(2), the "same fashion" conclusion). If the recovery `R` —
*a projective measurement `{Mᵢ}` followed by a conditional unitary `{Wᵢ}`*
(`ProjectiveUnitaryRecovery`) — corrects `E₁` on a code `C`, then its transform `R.conjugate U
V` — *again a projective measurement `{U Mᵢ U†}` followed by a conditional unitary `{V† Wᵢ
U†}}`* — corrects the equivalent channel `E₂ = U ∘ E₁ ∘ V` on the transported code `V† C`.

So the error-correction procedure for `E₂` is performed in the *same fashion* as that for `E₁`.
-/
theorem corrects_conjugate {ι : Type*} [Fintype ι] {E₁ : State S → State S} {C : Set (State S)}
    (R : ProjectiveUnitaryRecovery ι S) (U V : Evolution S) (hR : Corrects R.apply E₁ C) :
    Corrects (R.conjugate U V).apply (fun ρ => U.evolve (E₁ (V.evolve ρ)))
      (V.adjoint.evolve '' C) := sorry

end AxQM
