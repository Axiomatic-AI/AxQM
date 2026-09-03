/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Associator
import AxQM.Basic.API.BellBasis
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Support
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.Core.ConditionalEntropy
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch2.Exercise2_75
import AxQM.NC.Ch2.Exercise2_78
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState

/-!
# N&C Problem 11.3 — Analogue of the triangle inequality for conditional entropy

*(N&C p. 525.)*

Show H(X,Y|Z)>=H(X|Z), that S(A,B|C)>=S(A|C) can fail, and prove S(A,B|C)>=S(A|C)-S(B|C).

* `condEntropyPairGivenC` — the conditional entropy `S(A,B|C)` of a tripartite state.
* `condEntropyFirstGivenC` — the conditional entropy `S(A|C)` of a tripartite state.
* `exists_condEntropyPairGivenC_lt` — Part 2: a state with `S(A,B|C) < S(A|C)`.
* `condEntropySecondGivenC` — the conditional entropy `S(B|C)` of a tripartite state.
* `not_condEntropyPairGivenC_ge_condEntropyFirstGivenC_sub_condEntropySecondGivenC` — Part 3: N&C
  (11.136) is false as stated; a tripartite state violates `S(A,B|C) ≥ S(A|C) − S(B|C)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Conditional entropy of the pair given the conditioning system**, `S(A,B|C) = S(A,B,C) − S(C)`,
for a tripartite state on `A ⊗ (C ⊗ B)`. -/
def State.condEntropyPairGivenC (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  ρ.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy

/-- **Conditional entropy of the first system given the conditioning system**,
`S(A|C) = S(A,C) − S(C)`, for a tripartite state on `A ⊗ (C ⊗ B)`. It is the bipartite conditional
entropy (`State.condVonNeumannEntropy`) of the `A ⊗ C` marginal, read off by re-associating
`A ⊗ (C ⊗ B) ≃ (A ⊗ C) ⊗ B` and tracing out `B`. -/
def State.condEntropyFirstGivenC (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  (State.congr (QSystem.assoc A C B) ρ).reducedLeft.condVonNeumannEntropy

/-- **N&C Problem 11.3, Part 2: `S(A,B|C) ≥ S(A|C)` is not always true.** There is a tripartite
state whose conditional entropy of the pair `A, B` given `C` is strictly less than that of `A`
alone given `C` — in contrast with the classical bound `H(X,Y|Z) ≥ H(X|Z)` of Part 1. -/
theorem exists_condEntropyPairGivenC_lt :
    ∃ τ : State (qubit ⊗ (qubit ⊗ qubit)), τ.condEntropyPairGivenC < τ.condEntropyFirstGivenC :=
      sorry

/-- **Conditional entropy of the second system given the conditioning system**, `S(B|C) = S(B,C) −
S(C)`, for a tripartite state on `A ⊗ (C ⊗ B)`. Used to state N&C Problem 11.3, Part 3. -/
def State.condEntropySecondGivenC (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  ρ.reducedRight.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy

/-- **N&C Problem 11.3, Part 3: the "conditional triangle inequality" `S(A,B|C) ≥ S(A|C) − S(B|C)`
(Nielsen & Chuang eq. 11.136) is FALSE as stated.** No such inequality holds for all tripartite
states.

We refute the literal statement rather than silently repairing it to the genuinely-true form
`S(A,B|C) ≥ S(A|C) − S(B)` with the *unconditioned* `S(B)`. The inequality is written in its
`(S(A|C) − S(B|C)) ≤ S(A,B|C)` form. -/
theorem not_condEntropyPairGivenC_ge_condEntropyFirstGivenC_sub_condEntropySecondGivenC :
    ¬ ∀ τ : State (qubit ⊗ (qubit ⊗ qubit)),
      τ.condEntropyFirstGivenC - τ.condEntropySecondGivenC ≤ τ.condEntropyPairGivenC := sorry

end AxQM
