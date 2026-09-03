/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qudit
import AxQM.Basic.Observable
import AxQM.Concrete.PauliString
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM.Basic.API — the real Pauli expansion of a Hamiltonian (N&C Problem 4.3(2))

The **physics** half of part (2) of Nielsen & Chuang, Problem 4.3: *the Hamiltonian
`H = i ln(U)` can be written `H = Σ_g h_g g` with real `h_g`, the sum over all `n`-fold tensor
products `g` of the Pauli matrices `{I, X, Y, Z}`.* Here a Hamiltonian is an
`Observable` — a self-adjoint operator — and the `n`-qubit register is the
`2ⁿ`-level system `qudit (2ⁿ)`. The statement here consumes the `Observable` primitive: it says
that the matrix of *any* Hamiltonian on the `n`-qubit register, written in the computational
basis and reindexed to bit strings, is a **real**-coefficient combination of Pauli strings.

## Main declarations
* `Observable.stdMatrix` — the matrix of an observable (Hamiltonian) on `qudit d` in the
  **computational basis** `|0⟩, …, |d-1⟩` (the orthonormal `EuclideanSpace.basisFun`): the
  operator→matrix bridge for an `Observable`. (It represents a self-adjoint operator; the
  Trotter parts (4)/(5) instead need the matrices of the *unitary* evolutions `exp(-iHΔ)`, a
  distinct `Evolution`→matrix bridge, so `stdMatrix` does not serve them directly.)
* `Observable.exists_real_pauliString_expansion` — **Problem 4.3(2)**: for a Hamiltonian
  `H : Observable (qudit (2ⁿ))`, its computational-basis matrix reindexed to bit strings
  (`Fin n → Fin 2`) is `Σ_g (h_g : ℂ) • pauliString g` for real `h_g`.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **computational-basis matrix** of an observable (Hamiltonian) on the `d`-level register
`qudit d`: the matrix of `H.op` with respect to the orthonormal computational basis
`EuclideanSpace.basisFun`, whose `(i, j)` entry is `⟨i|H|j⟩ = ⟪|i⟩, H|j⟩⟫`. The operator→matrix
bridge for an `Observable` on `qudit d`. -/
def Observable.stdMatrix (H : Observable (qudit d)) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ) H.op.toLinearMap

/-- **Nielsen & Chuang, Problem 4.3(2).** -/
theorem Observable.exists_real_pauliString_expansion {n : ℕ} (H : Observable (qudit (2 ^ n))) :
    ∃ h : (Fin n → Fin 4) → ℝ,
      H.stdMatrix.submatrix finFunctionFinEquiv finFunctionFinEquiv
        = ∑ g, (h g : ℂ) • Concrete.pauliString g := sorry

end AxQM
