/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledControlledUnitary

/-!
# AxQM.Basic.API — Deutsch's one-bit algorithm

**Deutsch's algorithm** (the one-bit *Deutsch–Jozsa* problem, Nielsen & Chuang §1.4.3) determines,
with a **single** query to a function `f : {0,1} → {0,1}`, the global property `f(0) ⊕ f(1)` — i.e.
whether `f` is *constant* (`f(0) ⊕ f(1) = 0`) or *balanced* (`= 1`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {f : Fin 2 → Fin 2} {Uf : Evolution (qubit ⊗ qubit)}

/-- **The Deutsch circuit** `(H ⊗ I) · U_f · (H ⊗ H)` on two qubits (Nielsen & Chuang §1.4.3, Figure
1.19): a Hadamard on each qubit, the oracle `U_f`, then a final Hadamard on the query (first,
left) qubit. Here `U_f` is an arbitrary evolution; the physical content is fixed by the oracle
property `IsDeutschOracle`. -/
def deutschCircuit (Uf : Evolution (qubit ⊗ qubit)) : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onLeft qubit).comp (Uf.comp (hadamardGate ⊗ hadamardGate))

/-- **`U_f` is the (reversible) oracle for `f : {0,1} → {0,1}`** (Nielsen & Chuang §1.4.3): the XOR
oracle `U_f|x, y⟩ = |x, y ⊕ f(x)⟩`, i.e. it leaves the query register `|x⟩` alone and adds
`f(x)` into the answer register `|y⟩` (`⊕` is addition in `Fin 2`). -/
def IsDeutschOracle (f : Fin 2 → Fin 2) (Uf : Evolution (qubit ⊗ qubit)) : Prop :=
  ∀ x y : Fin 2, Uf.evolvePure (qubitBasis x ⊗ qubitBasis y) = qubitBasis x ⊗ qubitBasis (y + f x)

end AxQM
