/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.Basic.API.UnitaryBlochRotation
import AxQM.Concrete.PauliStringDiagonalize
import AxQM.Concrete.PauliStringCliffordConjugation
import AxQM.Concrete.SingleQubitWire

/-!
# The Problem 4.3(3) basis-change gate on a register wire, as an `Evolution`

Problem 4.3(3)'s `O(n)`-gate circuit for `exp(-i h_g g Δ)` opens with a layer `B = ⨂ₖ B_{gₖ}` of
single-qubit basis-change gates, one per wire: `B_{gₖ} = pauliDiagGate (gₖ)` diagonalises the Pauli
factor `σ_{gₖ}` to `Z` (Hadamard for `X`, `S·H` for `Y`, identity for `I`/`Z`).
To *count* that layer with the elementary-gate budget
`CircuitBudget` — which operates on the qubit control tower — each per-wire factor must first be a
named register `Evolution`.

## Main declarations
* `pauliDiagWireEvolution n t a` — `B_a` placed on wire `t` of the `2ⁿ`-level register, as an
  `Evolution (qudit (2ⁿ))`: the `quditGate` promotion of `singleQubitOnWire finFunctionFinEquiv t
  (pauliDiagGate a)`. The basis-change gate is indexed by the Pauli `a : Fin 4` rather
  than a real angle.
* `pauliDiagLayer n g` — **the whole basis-change layer** `B = ⨂ₖ B_{gₖ}` as one `Evolution (qudit
  (2ⁿ))`: the ordered product `∏_{t<n} pauliDiagWireEvolution n t (g t)` of the `n` per-wire gates
  (a `List.prod` over `List.finRange n`), the `n`-gate object opening Problem 4.3(3)'s circuit.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The Problem 4.3(3) basis-change gate `B_a` on a register wire, as an `Evolution`.** The
diagonalising gate `pauliDiagGate a` placed on wire `t` of the `2ⁿ`-level register `qudit (2ⁿ)`:
the `quditGate` promotion of `singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate a)`.
Taking `a = g t` over all wires `t` gives the
layer `B = ⨂ₖ B_{gₖ}` factor by factor. -/
def pauliDiagWireEvolution (n : ℕ) (t : Fin n) (a : Fin 4) : Evolution (qudit (2 ^ n)) :=
  quditGate
    (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t (pauliDiagGate_mem_unitaryGroup a))

/-- **The Problem 4.3(3) basis-change layer** `B = ⨂ₖ B_{gₖ}` as an `Evolution`. This is the
`n`-gate layer that opens Problem 4.3(3)'s `O(n)` circuit for `exp(-i h_g g Δ)`. -/
def pauliDiagLayer (n : ℕ) (g : Fin n → Fin 4) : Evolution (qudit (2 ^ n)) :=
  ((List.finRange n).map fun t => pauliDiagWireEvolution n t (g t)).prod

end

end AxQM
