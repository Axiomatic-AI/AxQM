/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HeisenbergSwap
import AxQM.Concrete.AxisAngleGateValues

/-!
# Concrete: universality of `√SWAP` — a `CNOT` from `√SWAP` and single-qubit gates

*Nielsen & Chuang, Exercise 7.52 (Universality of the Heisenberg Hamiltonian), Part 3.*
-/

open Matrix
open scoped Kronecker

namespace AxQM.Concrete

/-- The **two-qubit controlled-`NOT` gate** `CNOT` on `Fin 2 × Fin 2` with qubit 1 the control and
qubit 2 the target: `CNOT |a, b⟩ = |a, a + b⟩` (flip the target iff the control is `|1⟩`). A real
permutation matrix. -/
noncomputable def twoQubitCNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => if i = (j.1, j.1 + j.2) then 1 else 0

/-- The **`√SWAP` implementation of `CNOT`**: the explicit circuit conjugating the controlled-`Z`
construction `(S ⊗ S†) · √SWAP · (Z ⊗ 1) · √SWAP` by a Hadamard on the target qubit. -/
noncomputable def sqrtSwapHeisCNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ hadamardC)
    * ((sMatrix ⊗ₖ sMatrix.conjTranspose) * sqrtSwapHeis
        * (pauliZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * sqrtSwapHeis)
    * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ hadamardC)

/-- **Nielsen & Chuang, Exercise 7.52, Part 3 (the universality of `√SWAP`).** The `√SWAP` gate of
the Heisenberg exchange interaction, composed with single-qubit gates, implements a
controlled-`NOT`: `sqrtSwapHeisCNOT = e^{−iπ/4} · CNOT`. Since the global phase `e^{−iπ/4}` is
physically irrelevant, `√SWAP` is universal — the concluding claim of Exercise 7.52.
-/
theorem sqrtSwapHeisCNOT_eq :
    sqrtSwapHeisCNOT = Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) • twoQubitCNOT := sorry

end AxQM.Concrete
