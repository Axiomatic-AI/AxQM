/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.PauliGroup

/-!
# Concrete: the Pauli normalizer, and uniqueness up to global phase

Nielsen & Chuang **Theorem 10.6** — *any unitary `U` on `n` qubits with `U Gₙ U† ⊆ Gₙ` is, up to a
global phase, a product of `O(n²)` Hadamard/phase/CNOT gates*.

## Contents

* `IsPauliNormalizer U` — **the normalizer predicate.** `U` is unitary and conjugates every element
  of the Pauli group `Gₙ` back into `Gₙ`. This is exactly N&C's hypothesis "if `g ∈ Gₙ` then `U g U†
  ∈ Gₙ`", i.e. membership in the normalizer `N(Gₙ)`.

* `isPauliNormalizer_singleQubit_eq_smul_cliffordCircuit` — **Theorem 10.6 for a single qubit.**
  Every single-qubit Pauli normalizer is a global phase times an `H`/`S` Clifford circuit.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-- **The Pauli normalizer** `N(Gₙ)`. `U` is unitary and conjugates every element of the `n`-qubit
Pauli group `Gₙ` (through its faithful matrix representation `PauliGroup.toMat`, `p ↦ iˢ • P_a`)
back into `Gₙ`. This is exactly Nielsen & Chuang's hypothesis in Theorem 10.6: "if `g ∈ Gₙ` then
`U g U† ∈ Gₙ`". -/
def IsPauliNormalizer (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
    ∀ p : PauliGroup n, ∃ q : PauliGroup n, U * p.toMat * Uᴴ = q.toMat

/-- **Nielsen & Chuang Theorem 10.6 for a single qubit.** Every single-qubit Pauli normalizer `U`
equals a global phase times an `H`/`S` Clifford circuit: `∃ C, c, ‖c‖ = 1 ∧ U = c • C.toMatrix`.
This is the base case (`n = 1`) of the converse of Theorem 10.6. -/
theorem isPauliNormalizer_singleQubit_eq_smul_cliffordCircuit
    {U : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ (C : CliffordCircuit 1) (c : ℂ), ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C := sorry

end AxQM.Concrete

end
