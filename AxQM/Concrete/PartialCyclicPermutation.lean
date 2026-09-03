/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
/-!
# Concrete: the partial cyclic permutation of the three-qubit basis (N&C eq. 4.31)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.27 (p. 183) asks for a
circuit realising the `8 × 8` permutation matrix (4.31). Reading each column `j` of that matrix,
the induced permutation of the computational basis `|q₁ q₂ q₃⟩` (with value `4q₁ + 2q₂ + q₃`) fixes
`|000⟩` and cyclically shifts the seven non-zero basis states,
`1 → 2 → 3 → 4 → 5 → 6 → 7 → 1`.
-/

namespace AxQM.Concrete

/-- **The partial cyclic permutation of the three-qubit computational basis** (Nielsen & Chuang
eq. 4.31): the map on basis indices `(q₁, q₂, q₃) ∈ (Fin 2)³` that fixes `(0,0,0)` and cyclically
shifts the seven non-zero triples in order of their value `4q₁ + 2q₂ + q₃`, i.e.
`1 → 2 → 3 → 4 → 5 → 6 → 7 → 1`. Each output triple is column `4q₁ + 2q₂ + q₃` of the matrix
(4.31). -/
def partialCyclicShift : Fin 2 → Fin 2 → Fin 2 → Fin 2 × Fin 2 × Fin 2
  | 0, 0, 0 => (0, 0, 0)
  | 0, 0, 1 => (0, 1, 0)
  | 0, 1, 0 => (0, 1, 1)
  | 0, 1, 1 => (1, 0, 0)
  | 1, 0, 0 => (1, 0, 1)
  | 1, 0, 1 => (1, 1, 0)
  | 1, 1, 0 => (1, 1, 1)
  | 1, 1, 1 => (0, 0, 1)

end AxQM.Concrete
