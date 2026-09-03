/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringLocality

/-!
# Nielsen & Chuang, Exercise 10.50 — the five-qubit code saturates the quantum Hamming bound

*(N&C p. 469.)*

Show the five qubit code saturates the quantum Hamming bound (10.51 with equality).

* `quantumHammingBoundLHS`
* `fiveQubitCode_saturates_quantumHammingBound` — the exercise: `quantumHammingBoundLHS 5 1 1 = 2⁵`,
  i.e. (10.51) holds with *equality* for the five-qubit code.
-/

open scoped BigOperators

namespace AxQM

/-- The left-hand side of the **quantum Hamming bound** (N&C eq. (10.51)) for a code encoding `k`
qubits in `n` qubits and correcting every error on `t` or fewer qubits: the number of correctable
Pauli errors — the Pauli strings of weight `≤ t` on `n` qubits, `Concrete.localPauliStrings t n` —
times the code-space dimension `2ᵏ`. For a non-degenerate code these count the orthogonal
`2ᵏ`-dimensional error subspaces, which must fit inside the `2ⁿ`-dimensional register. -/
def quantumHammingBoundLHS (n k t : ℕ) : ℕ := (Concrete.localPauliStrings t n).card * 2 ^ k

/-- **Nielsen & Chuang, Exercise 10.50.** The five-qubit `[[5,1,3]]` code *saturates* the quantum
Hamming bound (10.51). So the inequality (10.51) holds with **equality** — the code is perfect. -/
theorem fiveQubitCode_saturates_quantumHammingBound :
    quantumHammingBoundLHS 5 1 1 = 2 ^ 5 := sorry

end AxQM
