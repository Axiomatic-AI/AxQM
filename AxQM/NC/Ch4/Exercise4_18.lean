/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Swap

/-!
# Nielsen & Chuang, Exercise 4.18 (Controlled-`Z` is symmetric between control and target)

*(N&C p. 179.)*

Show controlled-Z is symmetric between control and target qubits.

* `controlledZGate_swap_symm`
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.18: the controlled-`Z` gate is symmetric between control and
target.** Conjugating `controlledZGate` by the `SWAP` gate — the gate that interchanges the two
qubits — leaves it unchanged: `Evolution.swap · controlledZGate · Evolution.swap =
controlledZGate`, i.e. `SWAP · CZ · SWAP = CZ`. -/
theorem controlledZGate_swap_symm :
    (Evolution.swap (S := qubit)).comp (controlledZGate.comp (Evolution.swap (S := qubit)))
      = controlledZGate := sorry

end AxQM
