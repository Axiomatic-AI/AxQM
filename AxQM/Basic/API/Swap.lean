/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledZ

/-!
# AxQM.Basic.API — the SWAP gate and the symmetry of controlled-`Z`

The operator-level form of the two-qubit `SWAP` gate and the operator-level operator identity behind
Nielsen & Chuang Exercise 4.18 (the controlled-`Z` gate is symmetric between the control and target
qubits).

## Main declarations
* `Evolution.swap` — the **`SWAP` gate** `SWAP` on `S ⊗ S`, the closed-system evolution that
  exchanges the two factors of an identical-system composite. It is
  `Evolution.ofLinearIsometryEquiv` of the factor-swap `TensorProduct.commIsometry`,
  and its action is `SWAP(x ⊗ y) = y ⊗ x` (`Evolution.swap_op_tmul`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The `SWAP` gate** on `S ⊗ S` (Nielsen & Chuang §1.3.4): the closed-system `Evolution` that
exchanges the two factors of an identical-system composite, `SWAP(x ⊗ y) = y ⊗ x`. It is
`Evolution.ofLinearIsometryEquiv` of the factor-swap isometry `TensorProduct.commIsometry`, so it is
 with unitarity inherited from that isometry. -/
def Evolution.swap : Evolution (S ⊗ S) :=
  Evolution.ofLinearIsometryEquiv (TensorProduct.commIsometry ℂ S.space S.space)

/-- **Action of the `SWAP` gate** on a product vector: `SWAP(x ⊗ y) = y ⊗ x`. -/
@[simp]
theorem Evolution.swap_op_tmul (x y : S.space) :
    (Evolution.swap (S := S)).op (x ⊗ₜ[ℂ] y) = y ⊗ₜ[ℂ] x := by
  rw [Evolution.swap, Evolution.ofLinearIsometryEquiv_op_apply]
  exact TensorProduct.comm_tmul ℂ S.space S.space x y

end AxQM
