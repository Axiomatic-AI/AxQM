/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGenerators
import AxQM.Concrete.PauliStringEncodingLayers
import AxQM.Concrete.PauliStringCliffordCircuit

/-!
# Concrete: the `O(n²)` gate-count bound of the normalizer synthesis (N&C Theorem 10.6 /
Exercise 10.40, Fig 10.9)

*(Nielsen & Chuang, Theorem 10.6 / Exercise 10.40, §10.5.2, pp. 461–462.)*
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

/-- **Nielsen & Chuang, Theorem 10.6 (converse), with the `O(n²)` gate count.** Every `n`-qubit
Pauli normalizer `U` equals a global phase times a Clifford (`H`/`S`/`CNOT`) circuit `C` of
length **at most `9·n² + 105·n`**: `∃ C c, ‖c‖ = 1 ∧ U = c • C.toMatrix ∧ C.length ≤ 9·n² +
105·n`. -/
theorem isPauliNormalizer_eq_smul_cliffordCircuit_length_le {n : ℕ}
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ (C : CliffordCircuit n) (c : ℂ),
      ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C ∧ C.length ≤ 9 * n ^ 2 + 105 * n := sorry

/-- **Nielsen & Chuang, Theorem 10.6.** There is a *universal* constant `K` such that
every `n`-qubit Pauli normalizer `U` is a global phase times a Clifford circuit of `O(n²)`
gates: `∃ K, ∀ n U, IsPauliNormalizer U → ∃ C c, ‖c‖ = 1 ∧ U = c • C.toMatrix ∧ C.length ≤ K ·
n²`. -/
theorem isPauliNormalizer_eq_smul_cliffordCircuit_bigO :
    ∃ K : ℕ, ∀ (n : ℕ) (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
      IsPauliNormalizer U →
        ∃ (C : CliffordCircuit n) (c : ℂ),
          ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C ∧ C.length ≤ K * n ^ 2 := sorry

end AxQM.Concrete

end
