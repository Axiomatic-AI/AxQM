/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardGate

/-!
# Nielsen & Chuang, Exercise 2.52

*(N&C p. 82.)*

Verify H^2 = I.

* `hadamardGate_sq`
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.52: `H² = I`.** The Hadamard gate `hadamardGate : Evolution
qubit` squares to the identity evolution in the gate monoid: `hadamardGate ^ 2 = 1`. -/
theorem hadamardGate_sq : hadamardGate ^ 2 = 1 := sorry

end AxQM
