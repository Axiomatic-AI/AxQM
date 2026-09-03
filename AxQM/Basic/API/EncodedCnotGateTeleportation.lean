/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GateTeleportProtocolReshape
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation

/-!
# AxQM.Basic.API — encoded (logical) CNOT gate teleportation

The verifiable mathematical core of **Nielsen & Chuang Problem 10.5**: a fault-tolerant `CNOT`
between two logical qubits of an `[n, 1]` stabilizer code, implemented by **gate teleportation** —
the same Gottesman–Chuang construction that Problem 4.6 uses to implement a *physical* `CNOT`, now
run so that the two output halves land *encoded in the code*.  The two output code blocks are then
genuine logical qubits carrying the logical `CNOT` of the input data, up to a pair of **logical
Pauli** byproducts — Pauli operators, hence correctable by normalizer gates applied transversally.

## The construction, and what it reduces to

* `encodedCnotGateTeleportation_identity` — the **encoded CNOT gate-teleportation identity**:
  applying `id ⊗ (E ⊗ E)` (encode the two output blocks, leave the two Bell-measured pairs alone) to
  the reshaped teleportation register `reshape ((q_A ⊗ q_B) ⊗ |χ⟩)` gives `¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩)
  ⊗ (E ⊗ E)((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT (q_A ⊗ q_B)))`, `p = (x₁,y₁)`, `q = (x₂,y₂)`.
  Bell-measuring the two pairs (outcomes `p, q`) therefore leaves the two *encoded* output blocks in
  `(E ⊗ E)((C_A ⊗ C_B)(CNOT(q_A ⊗ q_B)))` — the encoded, byproduct- corrected `CNOT` of the input
  data — which the logical Pauli correction `(E ∘ C_A ∘ E†) ⊗ (E ∘ C_B ∘ E†)` (applied
  transversally) undoes, leaving the logical `CNOT` `(E ⊗ E)(CNOT(q_A ⊗ q_B))` on the two logical
  qubits.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {C : QSystem}

/-- **The encoded (logical) CNOT gate-teleportation identity** (Nielsen & Chuang Problem 10.5).
Since the byproducts are Pauli operators, their encoded form `E ∘ C ∘ E†` is a *logical* Pauli
(a normalizer gate, applied transversally), and correcting it leaves the logical `CNOT` `(E ⊗
E)(CNOT(q_A ⊗ q_B))` on the two logical qubits — the fault-tolerant `CNOT` between two logical
qubits of Problem 10.5. -/
theorem encodedCnotGateTeleportation_identity (E : qubit.space →ₗ[ℂ] C.space)
    (qA qB : qubit.space) :
    TensorProduct.map
        (LinearMap.id : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →ₗ[ℂ]
          ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space)
        (TensorProduct.map E E)
        (gateTeleportProtocolReshape.toIsometry
          ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] cnotGateTeleportResource.vec))
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
            TensorProduct.map E E
              ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
                (cnotGate.op (qA ⊗ₜ[ℂ] qB))) := sorry

end AxQM
