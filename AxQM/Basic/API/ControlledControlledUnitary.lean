/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.QubitThree
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the doubly-controlled gate `C²(U)` and three-qubit machinery

Infrastructure for Nielsen & Chuang's **multiply-controlled** operations
(N&C §4.3, eq. 4.29): the doubly-controlled gate `C²(U)` and the tools needed to verify
three-qubit circuit identities against it (e.g. Exercise 4.21 — Figure 4.8).

## Main declarations
* **Factorised action of composite evolutions.** `Evolution.onRight_evolvePure` — the Schrödinger
  action of `1 ⊗ V` on a product pure state, definitional (`mapL` on a pure tensor is factorwise).
* `ccontrolledUnitary U` — the **doubly-controlled gate** `C²(U) = C(C(U))` on the three-qubit
  system `qubit ⊗ (qubit ⊗ qubit)`: apply the single-qubit unitary `U` to the last qubit exactly
  when *both* of the first two ("control") qubits are `|1⟩` (N&C eq. 4.29 with `n = 2`, `k = 1`).
  It is literally the single-qubit-controlled gate `controlledUnitary` applied twice, so it is a
  genuine `Evolution` (its unitarity is inherited, no new obligation).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A gate on the right factor acts only there:** `(1 ⊗ V)(ψ ⊗ φ) = ψ ⊗ (Vφ)`. -/
theorem Evolution.onRight_evolvePure (V : Evolution T) (S : QSystem)
    (ψ : PureState S) (φ : PureState T) :
    (V.onRight S).evolvePure (ψ ⊗ φ) = ψ ⊗ (V.evolvePure φ) := by
  apply PureState.ext; rfl

/-- **The doubly-controlled gate** `C²(U)` (Nielsen & Chuang eq. 4.29, `n = 2`, `k = 1`) on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)`: the single-qubit unitary `U` is applied to the
last qubit exactly when *both* of the first two control qubits are `|1⟩`. It is the
single-controlled gate `controlledUnitary` iterated once, `C²(U) = C(C(U))`: the outer control
is the first qubit and its target is the two-qubit gate `C(U)` conditioning on the second qubit. -/
def ccontrolledUnitary (U : Evolution qubit) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (controlledUnitary U)

/-- **The Toffoli gate** (controlled-controlled-`NOT`, `C²(X)`; Nielsen & Chuang §1.3.4) on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)`: it flips the last (target) qubit exactly when
*both* of the first two control qubits are `|1⟩`. The canonical two-control gate, reused
throughout Chapter 4 (Exercises 4.24–4.27). -/
def toffoliGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) := ccontrolledUnitary pauliXGate

end AxQM
