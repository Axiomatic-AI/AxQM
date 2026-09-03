/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Core.CircuitBudget
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Core.TensorPowMultiControlledX
import AxQM.Basic.API.BlockGatePlacement
import AxQM.Core.McNotCircuitEvolution
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import AxQM.Basic.API.Evolution
import AxQM.Concrete.MultiControlledNotAsymptotics

/-!
# Nielsen & Chuang, Exercise 4.30 — a `Cⁿ(U)` circuit for general `n` using no work qubits

*(N&C p. 184.)*

Find an O(n^2)-gate circuit implementing C^n(U) with no work qubits.

* `barencoNCircuit` — the no-work-qubit circuit for `C^(k+1)(U)`.
* `mcCtrl_controlledUnitary_circuitBudget` — its gate budget, for every single-qubit `U`:
  `CircuitBudget (Cⁿ(U)) (8k(k+1)+2) (2k+3)`.
* `exists_barencoNCircuit_eq_mcCtrl`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The general no-work-qubit circuit -/

/-- **The Exercise 4.30 circuit** for `C^(k+1)(U)`, `U = (V 1)²`, with no work qubits. Given the
single-qubit square-root chain `V : ℕ → Evolution qubit` (with `(V (j+1))² = V j`), `barencoNCircuit
V k d` is the fully unfolded `k`-level Barenco reduction on `qtower k (qubit ⊗ qtower d qubit)`,
where `d` is the current depth (the number of already-peeled controls now idle in the target
module). The recursion expands the leading multiplexer of each layer:

* depth `d`, level `0`: the single-controlled reduction
  `barencoReductionCircuit 0 (unCtrl d (V (d+1)))`;
* depth `d`, level `k+1`: the deeper circuit (at depth `d+1`, reassociated onto the parent register
  by `qtower_qubit_comm`) composed with this layer's tail `barencoTail (k+1) (unCtrl d (V (d+1)))`.

Every root `V (d+1)` is a single-qubit gate lifted `d` times by idle wraps (`unCtrl d`) so that it
targets the innermost qubit. The whole circuit is thus built only from single-qubit-controlled gates
`C(Vⱼ)`, `C(Vⱼ†)` and multiply-controlled `NOT`s `Cᵏ(X)` — no ancilla. -/
def barencoNCircuit (V : ℕ → Evolution qubit) :
    (k d : ℕ) → Evolution (qtower k (qubit ⊗ qtower d qubit))
  | 0, d => barencoReductionCircuit 0 (unCtrl d (V (d + 1)))
  | k + 1, d =>
      (cast (congrArg Evolution (qtower_qubit_comm k (qubit ⊗ qtower d qubit)))
          (barencoNCircuit V k (d + 1))).comp
        (barencoTail (k + 1) (unCtrl d (V (d + 1))))

/-! ### The `O(n²)` gate budget of the circuit -/

/-- **Nielsen & Chuang, Exercise 4.30 — the `O(n²)` gate count of `Cⁿ(U)`.** For *every*
single-qubit unitary `U` and every `k`, the multiplexer `Cⁿ(U) = mcCtrl k (controlledUnitary U)`
(`n = k + 1` controls) has

`CircuitBudget (Cⁿ(U)) (8·k·(k+1) + 2) (2·k + 3)`,

i.e. it is realised — on exactly the `n + 1`-qubit register, **no work qubit** — by a circuit
built from at most `8k(k+1) + 2 = O(n²)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and at
most `2k + 3 = O(n)` single-qubit(-controlled) gates.
-/
theorem mcCtrl_controlledUnitary_circuitBudget (U : Evolution qubit) (k : ℕ) :
    CircuitBudget (mcCtrl k (controlledUnitary U)) (8 * k * (k + 1) + 2) (2 * k + 3) := sorry

/-- **Nielsen & Chuang, Exercise 4.30 (existence, fully faithful).** For *every* single-qubit
unitary `U` and every `k`, there is a single-qubit square-root chain `V` (with `V 0 = U`) such that
the `(k+1)`-controlled gate `C^(k+1)(U)` equals the explicit no-work-qubit circuit
`barencoNCircuit V k 0` — built only from single-qubit-controlled gates and multiply-controlled
`NOT`s. No square-root hypotheses are imposed: writing `n = k + 1`, this is the `Cⁿ(U)`
no-work-qubit circuit Exercise 4.30 asks for, for arbitrary `n`. -/
theorem exists_barencoNCircuit_eq_mcCtrl (U : Evolution qubit) (k : ℕ) :
    ∃ V : ℕ → Evolution qubit, V 0 = U ∧
      mcCtrl k (controlledUnitary U) = barencoNCircuit V k 0 := sorry

end AxQM
