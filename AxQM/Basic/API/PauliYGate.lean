/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary

/-!
# AxQM.Basic.API — the Pauli-`Y` gate

The **Pauli-`Y` gate** as a closed-system `Evolution` of the qubit, completing the Pauli gate
family (`pauliXGate`, `pauliZGate`).  It is the
missing single-qubit generator needed to state the `Y`-conjugation circuit identities of Nielsen &
Chuang **Exercise 4.31** (`CY₁C = Y₁X₂`, `CY₂C = Z₁Y₂`).

## Main declarations
* `pauliYGate` — `Y` as an `Evolution qubit`: its operator is `Concrete.pauliY = !![0,-i; i,0]`
  promoted through `Matrix.toEuclideanCLM`, with unitarity transported from
  `Concrete.pauliY_mem_unitaryGroup` (exactly as `pauliZGate` promotes `Concrete.pauliZ`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Pauli-`Y` gate** `Y` as a closed-system `Evolution` of the qubit. -/
def pauliYGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliY
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.pauliY_mem_unitaryGroup

end AxQM
