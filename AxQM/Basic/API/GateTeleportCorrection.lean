/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GateTeleportMeasurement

/-!
# AxQM.Basic.API — the deterministic `CNOT` of gate teleportation

The **correction step** of the Gottesman–Chuang gate-teleportation protocol for `CNOT` (Nielsen &
Chuang **Problem 4.6**).  Bell-measuring the two pairs leaves the two output qubits in
`CNOT (q_A ⊗ q_B)` *up to* the outcome-determined pair of single-qubit Pauli byproducts.  This file
undoes those byproducts, so that the protocol implements `CNOT` **deterministically**: whatever the
Bell-measurement outcome `(p, q)`, applying the outcome-determined single-qubit correction to the
output pair recovers the *same* state `CNOT (q_A ⊗ q_B)`.
-/

namespace AxQM

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

/-- **The gate-teleportation correction gate** for Bell-measurement outcome `(p, q) =
((x₁,y₁),(x₂,y₂))`. It is built entirely from single-qubit unitaries — resource #1 of
Problem 4.6. -/
noncomputable def gateTeleportCorrection (p q : Fin 2 × Fin 2) : Evolution (qubit ⊗ qubit) :=
  (pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).adjoint

end AxQM
