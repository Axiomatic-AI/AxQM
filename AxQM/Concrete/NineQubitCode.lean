/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: the nine-qubit Shor code stabilizer generators (Nielsen & Chuang Figure 10.11)

The eight stabilizer generators of the **nine-qubit Shor code** `[[9,1,3]]`, as Pauli-string index
vectors `Fin 9 → Fin 4` (`I = 0, X = 1, Y = 2, Z = 3`).
-/

namespace AxQM.Concrete

/-- The eight **nine-qubit Shor code generators** of Figure 10.11 as Pauli-string index vectors
`Fin 8 → (Fin 9 → Fin 4)` (`I = 0, X = 1, Y = 2, Z = 3`): six `Z`-type bit-flip checks
`Z₁Z₂, Z₂Z₃, Z₄Z₅, Z₅Z₆, Z₇Z₈, Z₈Z₉` and two `X`-type phase-flip checks `X₁⋯X₆, X₄⋯X₉`. -/
def shorGenIdx : Fin 8 → (Fin 9 → Fin 4) :=
  ![![3, 3, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 3, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 3, 3],
    ![1, 1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 1, 1]]

end AxQM.Concrete
