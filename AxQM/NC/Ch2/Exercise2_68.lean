/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellState
import AxQM.Concrete.PauliEigenvectors
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Nielsen & Chuang, Exercise 2.68 (the Bell state is not a product state)

*(N&C p. 96.)*

Prove (|00>+|11>)/sqrt2 is not a product state |a>|b>.

* `bellPhiPlus_ne_tmul` — `bellPhiPlus ≠ a ⊗ b` for *all* single-qubit pure states `a, b`.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.68.** The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` is not a product
state: `bellPhiPlus ≠ a ⊗ b` for every pair of single-qubit pure states `a, b`. Equivalently,
`|Φ⁺⟩` is *entangled* — it cannot be factored across the two qubits. -/
theorem bellPhiPlus_ne_tmul (a b : PureState qubit) : bellPhiPlus ≠ a ⊗ b := sorry

end AxQM
