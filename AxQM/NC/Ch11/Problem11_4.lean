/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.Core.ConditionalEntropy
import AxQM.ToMathlib.Analysis.SpecialFunctions.ConditionalEntropy

/-!
# N&C Problem 11.4 — Conditional forms of strong subadditivity

*(N&C p. 526.)*

Conditional forms of strong subadditivity: prove quantum form; show classical analogue can fail.

* `condEntropyTripleGivenD` — the conditional entropy `S(A, B, C | D)` of a state on
  `A ⊗ ((B ⊗ D) ⊗ C)`.
* `condEntropyMiddleGivenD` — the conditional entropy `S(B | D)`.
* `condEntropyLeftPairGivenD` — the conditional entropy `S(A, B | D)`.
* `condEntropyRightPairGivenD` — the conditional entropy `S(B, C | D)`.
* `condEntropy_add_le_add` — Part (1): conditional strong subadditivity `S(A, B, C | D) + S(B | D) ≤
  S(A, B | D) + S(B, C | D)`, for every state (no faithfulness hypothesis).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C D : QSystem}

/-- **`S(A, B, C | D) = S(A, B, C, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional
entropy of the whole non-`D` part given `D`. -/
def State.condEntropyTripleGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  ρ.vonNeumannEntropy - ρ.reducedRight.reducedLeft.reducedRight.vonNeumannEntropy

/-- **`S(B | D) = S(B, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional entropy of
the middle system `B` given `D`. -/
def State.condEntropyMiddleGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  ρ.reducedRight.reducedLeft.condVonNeumannEntropy

/-- **`S(A, B | D) = S(A, B, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional
entropy of the pair `A, B` given `D`. The `A ⊗ (B ⊗ D)` marginal is read off by re-associating
`A ⊗ ((B ⊗ D) ⊗ C) ≃ (A ⊗ (B ⊗ D)) ⊗ C` and tracing out `C`; `S(D)` is shared with the other
conditional entropies. -/
def State.condEntropyLeftPairGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  (ρ.congr (QSystem.assoc A (B ⊗ D) C)).reducedLeft.vonNeumannEntropy
    - ρ.reducedRight.reducedLeft.reducedRight.vonNeumannEntropy

/-- **`S(B, C | D) = S(B, C, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional
entropy of the pair `B, C` given `D`. -/
def State.condEntropyRightPairGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  ρ.reducedRight.vonNeumannEntropy
    - ρ.reducedRight.reducedLeft.reducedRight.vonNeumannEntropy

/-- **N&C Problem 11.4(1): conditional strong subadditivity of the von Neumann entropy.** For
**every** state `ρ` on `A ⊗ ((B ⊗ D) ⊗ C)`,

`S(A, B, C | D) + S(B | D) ≤ S(A, B | D) + S(B, C | D)`.

No faithfulness (`IsStrictlyPositive`) hypothesis is needed, matching N&C. -/
theorem State.condEntropy_add_le_add (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) :
    ρ.condEntropyTripleGivenD + ρ.condEntropyMiddleGivenD ≤
      ρ.condEntropyLeftPairGivenD + ρ.condEntropyRightPairGivenD := sorry

end AxQM
