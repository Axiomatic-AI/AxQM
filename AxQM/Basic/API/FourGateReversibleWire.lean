/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditGate
import AxQM.Concrete.QftGateCircuit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli
import AxQM.Concrete.MultiControlledNotCircuit

/-!
# The reversible ≤ 2-control gates on a register wire (N&C Exercise 4.43, four-gate bridge —
reversible register-lift stage, register-side ingredient)

The four-gate universality bridge's **reversible** generator family is the `≤ 2`-control
permutation gates — the `Toffoli`/`CNOT`/`NOT` gates `permGate enc (mcNotPerm S t)` with
`|S| ≤ 2`.

## Main declarations
* `mcNotWireEvolution n S t ht` — the multiply-controlled `NOT` with controls `S` and target `t`
  placed on the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`: the `quditGate` promotion
  of the permutation matrix `Concrete.permGate finFunctionFinEquiv (mcNotPerm S ht)`.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The multiply-controlled `NOT` on a register wire set.** The reversible gate with controls `S :
Finset (Fin n)` and target `t ∉ S` placed on the `2ⁿ`-level register, as a named `Evolution
(qudit (2ⁿ))`. For `|S| ≤ 2` this is the `Toffoli`/`CNOT`/`NOT` addressed to the wires
`(S, t)`. -/
def mcNotWireEvolution (n : ℕ) (S : Finset (Fin n)) (t : Fin n) (ht : t ∉ S) :
    Evolution (qudit (2 ^ n)) :=
  quditGate (permGate_mem_unitaryGroup finFunctionFinEquiv (mcNotPerm S ht))

end

end AxQM
