/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.CoherentInformation

/-!
# N&C Theorem 12.10 — the quantum data processing inequality

*(N&C p. 564.)*

Quantum data processing inequality: S(rho) >= I(rho,E1) >= I(rho,E2 o E1).

* `coherentInfoComp_le_coherentInfo`
-/

noncomputable section

namespace AxQM

variable {Q C : QSystem}

/-- **Second inequality of the quantum data processing inequality** (Nielsen & Chuang Theorem 12.10,
eq. (12.119), second stage):

`I(ρ, E2 ∘ E1) ≤ I(ρ, E1)`.

The composed coherent information `I(ρ, E2 ∘ E1)` (`State.coherentInfoComp`, the state coherent
information of the twice-processed reference–system state `R''Q''`) is at most the
single-channel coherent information `I(ρ, E1)` (`ρ.coherentInfo U₁ ω₁`).
-/
theorem State.coherentInfoComp_le_coherentInfo (ρ : State Q) (U₁ : Evolution (Q ⊗ C))
    (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.coherentInfoComp U₁ ω₁ U₂ ω₂ ≤ ρ.coherentInfo U₁ ω₁ := sorry

end AxQM
