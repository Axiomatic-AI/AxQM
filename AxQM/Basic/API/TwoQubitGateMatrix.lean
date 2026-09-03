/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.Qubit
import AxQM.Basic.Composite
import AxQM.Concrete.Hadamard
import AxQM.Concrete.PauliKronecker

/-!
# AxQM.Basic.API — the computational-basis matrix of a two-qubit gate (N&C Ex 4.16)

The operator-level form of Nielsen & Chuang's Exercise 4.16: the `4 × 4` matrix, in the
computational basis, of a gate acting on a two-qubit register `qubit ⊗ qubit`, and — the
exercise's answer — the matrices of the **Hadamard gate applied to one qubit** of the register:
`H ⊗ I` (Hadamard on the top/first qubit, `hadamardGate.onLeft qubit`) and `I ⊗ H` (Hadamard on
the bottom/second qubit, `hadamardGate.onRight qubit`).

## Main declarations
* `Evolution.twoQubitStdMatrix` — the operator→matrix bridge for an `Evolution` on the two-qubit
  register `qubit ⊗ qubit`: its matrix in the computational **product** basis `{|i⟩ ⊗ |j⟩}` (indexed
  by `Fin 2 × Fin 2`), whose `(i, j)` entry is the matrix element `⟨i|U|j⟩ = ⟪|i⟩, U|j⟩⟫`. This is
  the two-qubit-composite analogue of `Observable.stdMatrix`, built directly from `⟪·, U·⟫` on the
  tensor-product orthonormal basis so it needs no change-of-basis apparatus on the composite space.
* `hadamardOnLeft_flattenFin4` / `hadamardOnRight_flattenFin4` — the same, flattened to the explicit
  `4 × 4` arrays of N&C's answer, in the big-endian basis order `00, 01, 10, 11`.
-/

open scoped InnerProductSpace TensorProduct Kronecker

open Matrix AxQM.Concrete

noncomputable section

namespace AxQM

/-- The **computational-basis matrix** of an evolution on the two-qubit register `qubit ⊗ qubit`. -/
def Evolution.twoQubitStdMatrix (U : Evolution (qubit ⊗ qubit)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => inner ℂ (qubitBasis i.1 ⊗ qubitBasis i.2).vec
    (U.op (qubitBasis j.1 ⊗ qubitBasis j.2).vec)

/-- **Nielsen & Chuang, Exercise 4.16 (first circuit), explicit `4 × 4` matrix.** In the big-endian
computational basis `00, 01, 10, 11`, the Hadamard gate on the top qubit of a two-qubit register
has matrix `(1/√2) !![1,0,1,0; 0,1,0,1; 1,0,-1,0; 0,1,0,-1]` — the flattening of `H ⊗ I`. -/
theorem hadamardOnLeft_flattenFin4 :
    flattenFin4 (hadamardGate.onLeft qubit).twoQubitStdMatrix
      = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] := sorry

/-- **Nielsen & Chuang, Exercise 4.16 (second circuit), explicit `4 × 4` matrix.** In the
big-endian computational basis `00, 01, 10, 11`, the Hadamard gate on the bottom qubit of a
two-qubit register has matrix `(1/√2) !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]` — the flattening of
`I ⊗ H`. -/
theorem hadamardOnRight_flattenFin4 :
    flattenFin4 (hadamardGate.onRight qubit).twoQubitStdMatrix
      = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1] := sorry

end AxQM
