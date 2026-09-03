/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.GateCircuit
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.Qubit

/-!
# Nielsen & Chuang, Exercise 4.22 (a `C²(U)` gate needs ≤ 8 one-qubit gates and 6 CNOTs)

*(N&C p. 181.)*

Prove a C^2(U) gate needs at most eight one-qubit gates and six CNOTs.

* `ccontrolledUnitary_gateCount_le`
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap Matrix

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.22.** For every single-qubit gate `U`, the doubly-controlled gate
`C²(U)` (`ccontrolledUnitary U`) is implemented by a typed circuit `gs` over `qubit ⊗ (qubit ⊗
qubit)` using **at most eight one-qubit gates and six CNOTs**. -/
theorem ccontrolledUnitary_gateCount_le (U : Evolution qubit) :
    ∃ gs : List Gate3, gateCircuit gs = ccontrolledUnitary U
      ∧ oneQubitCount gs ≤ 8 ∧ cnotCount gs ≤ 6 := sorry

end AxQM
