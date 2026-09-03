/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Associator
import AxQM.Basic.API.Entropy
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.Basic.API.ArakiLiebEqualityConditions
import AxQM.NC.Ch11.Theorem11_10

/-!
# General (faithfulness-free) strong subadditivity of the von Neumann entropy

* `vonNeumannEntropy_add_le_add'` — strong subadditivity `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` for an
  arbitrary state `ρ` on `A ⊗ (B ⊗ C)`.
-/

open Filter
open scoped Topology TensorProduct InnerProductSpace

noncomputable section

namespace AxQM

variable {A B C : QSystem}

set_option maxHeartbeats 800000 in
-- The four nested-tensor marginal entropies of `A ⊗ (B ⊗ C)` are costly to elaborate together,
-- exceeding the default heartbeat budget.
/-- **Strong subadditivity of the von Neumann entropy, general form** (Nielsen & Chuang, Theorem
11.14, eq. (11.73)): for an **arbitrary** state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`.

This is the faithfulness-free form: it carries no `IsStrictlyPositive ρ.op` hypothesis, matching
N&C's statement.
-/
theorem State.vonNeumannEntropy_add_le_add' (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.vonNeumannEntropy + ρ.reducedRight.reducedLeft.vonNeumannEntropy ≤
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy +
        ρ.reducedRight.vonNeumannEntropy := sorry

end AxQM
