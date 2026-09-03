/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Teleportation

/-!
# AxQM.Basic.API — Encoding an unknown qubit by teleportation

The verifiable mathematical core of **Nielsen & Chuang Problem 10.4** ("Encoding by
teleportation"): teleporting an *unknown* qubit `|ψ⟩` into the logical qubit of a stabilizer code,
using the *partially encoded* resource state `(|0⟩|0_L⟩ + |1⟩|1_L⟩)/√2` and a Bell-basis
measurement, with logical Pauli byproduct corrections.  This is the standard §1.3.7 teleportation
protocol with **Bob's half of the Bell pair replaced by the encoder's image**
in the code space, so that the teleported qubit lands *already encoded*.

## Main declarations
* `encoderBellVec E` — the **partially encoded resource vector**
  `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2 = (I ⊗ E)|Φ⁺⟩` on `qubit ⊗ C` (N&C eq. 10.126, the state prepared in
  part (1)): Bob's half of a Bell pair pushed through the encoder `E`.
* `encodingTeleportation_identity` — the **encoding-teleportation identity**: for an arbitrary qubit
  `|ψ⟩`, re-associating `|ψ⟩ ⊗ (partially encoded resource)` and grouping the first two qubits gives
  `|ψ⟩ ⊗ resource = ½ Σ_{x,y} |β_xy⟩ ⊗ E(X^y Z^x |ψ⟩)`. A Bell measurement of the first pair (part
  (2)) therefore leaves the code register in `E(X^y Z^x |ψ⟩) = X_L^y Z_L^x |ψ_L⟩` — the encoded
  input up to the *logical* Pauli byproduct `E ∘ (X^y Z^x) ∘ E†`, undone by the same outcome-indexed
  correction `pauliByproduct x y` applied logically (part (3)).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {C : QSystem}

/-- The **unnormalised partially encoded vector** `|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩` on `qubit ⊗ C`, where the
logical codewords are the encoder images `|0_L⟩ = E|0⟩`, `|1_L⟩ = E|1⟩`.  Its norm is `√2` for an
isometric encoder; the normalised resource is `encoderBellVec`.
Built directly from the tensor of basis vectors (like `bellVec`), so it presents the composite
`(qubit ⊗ C).space` head that the scalar-factoring lemmas want. -/
def encoderBellUnnormVec (E : qubit.space →ₗ[ℂ] C.space) : (qubit ⊗ C).space :=
  (qubitBasis 0).vec ⊗ₜ[ℂ] E (qubitBasis 0).vec + (qubitBasis 1).vec ⊗ₜ[ℂ] E (qubitBasis 1).vec

/-- The **partially encoded resource vector** `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` on `qubit ⊗ C`
(Nielsen & Chuang eq. 10.126), where the logical codewords are the encoder images
`|0_L⟩ = E|0⟩`, `|1_L⟩ = E|1⟩`.  Equivalently `(I ⊗ E)|Φ⁺⟩`: Bob's half of a shared Bell pair
pushed through the code encoder `E`. -/
def encoderBellVec (E : qubit.space →ₗ[ℂ] C.space) : (qubit ⊗ C).space :=
  (Real.sqrt 2 : ℂ)⁻¹ • encoderBellUnnormVec E

/-- **The encoding-teleportation identity** (Nielsen & Chuang Problem 10.4): for an arbitrary qubit
state `|ψ⟩` and a code encoder `E`, re-associating `|ψ⟩ ⊗ (|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` and
grouping the first two qubits gives `|ψ⟩ ⊗ (partially encoded resource) = ½ Σ_{x,y} |β_xy⟩ ⊗
E(X^y Z^x |ψ⟩)`. Measuring the first pair in the Bell basis therefore leaves the code register
in the *encoded* byproduct-corrected state `E(X^y Z^x |ψ⟩)`, which the logical Pauli correction
(the byproduct `pauliByproduct x y` conjugated into the code) undoes — teleportation directly
into the logical qubit. -/
theorem encodingTeleportation_identity (E : qubit.space →ₗ[ℂ] C.space) (v : qubit.space) :
    (QSystem.assoc qubit qubit C).toIsometry (v ⊗ₜ[ℂ] encoderBellVec E)
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          bellBasisVec p.1 p.2 ⊗ₜ[ℂ] E ((pauliByproduct p.1 p.2).op v) := sorry

end AxQM
