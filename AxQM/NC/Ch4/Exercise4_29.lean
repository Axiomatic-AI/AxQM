/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch4.Exercise4_30
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.CircuitBudget
import AxQM.Core.MultiControlledReduction
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Core.TensorPowMultiControlledX
import AxQM.Basic.API.BlockGatePlacement
import AxQM.Core.McNotCircuitEvolution
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Concrete.MultiControlledNotAsymptotics

/-!
# Nielsen & Chuang, Exercise 4.29 — a no-work-qubit `O(n²)` circuit for `Cⁿ(X)`

*(N&C p. 184.)*

Find an O(n^2)-gate circuit implementing C^n(X) with no work qubits.

* `cnx_circuitBudget`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### Face 3 — the fused `O(n²)` gate count on exactly `n + 1` wires -/

/-- **Nielsen & Chuang, Exercise 4.29 — Face 3 (the fused gate budget for `Cⁿ(X)` on exactly `n + 1`
wires).** The `n`-controlled `NOT` `Cⁿ(X) = mcCtrl k (controlledUnitary pauliXGate)` (`n = k +
1`) equals — on exactly the `n + 1`-qubit register, **no work qubit** — an explicit circuit
built from at most

`8k(k+1) + 2 = O(k²)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`), and `2k + 3 = O(k)`
single-qubit(-controlled) gates `C(Vⱼ)`, `C(Vⱼ†)`, `V₀`.

This is the missing fusion of the two earlier faces.
-/
theorem cnx_circuitBudget (k : ℕ) :
    CircuitBudget (mcCtrl k (controlledUnitary pauliXGate))
      (8 * k * (k + 1) + 2) (2 * k + 3) := sorry

/-! The `O(n²)` read-off of `cnx_circuitBudget`'s counts — that the total
-/

end AxQM
