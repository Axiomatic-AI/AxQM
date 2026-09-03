/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.GateCircuit
import AxQM.Basic.API.TwoLevelUnitaryCircuit
import AxQM.Basic.API.ControlPairGates
import AxQM.Basic.Composite
import AxQM.NC.Ch4.Exercise4_20
import AxQM.NC.Ch4.Exercise4_22

/-!
# Nielsen & Chuang, Exercise 4.39 (a circuit for a two-level unitary)

*(N&C p. 193.)*

Find a circuit of single-qubit and CNOT gates implementing a given two-level unitary.

* `exists_gateCircuit_twoLevelUnitaryCircuit` — for every single-qubit `Ũ`, there is a circuit `gs :
  List Gate3` (single-qubit gates and `CNOT`s only) with `gateCircuit gs = twoLevelUnitaryCircuit
  Ũ`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The routing and the full circuit -/

/-- **Nielsen & Chuang, Exercise 4.39.** For every single-qubit unitary `Ũ`, the two-level unitary
(4.60) is implemented by a circuit built from single-qubit gates and `CNOT`s.
-/
theorem exists_gateCircuit_twoLevelUnitaryCircuit (u : Evolution qubit) :
    ∃ gs : List Gate3, gateCircuit gs = twoLevelUnitaryCircuit u := sorry

end AxQM
