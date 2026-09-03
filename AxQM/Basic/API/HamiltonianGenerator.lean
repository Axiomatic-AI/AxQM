/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.CStarAlgebra.Unitary.Exp
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The Hamiltonian generator of a unitary evolution, with bounded spectrum

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 4.3(1) asks to show that,
for a unitary `U` on `n` qubits, `H ≡ i ln(U)` is **Hermitian, with eigenvalues in the range `0` to
`2π`**. Here a closed-system dynamics is an `Evolution` (a bundled unitary) and a
Hamiltonian is an `Observable` (a bundled self-adjoint operator); `Observable.propagator H 1 0 1` is
the unit-time, `ℏ = 1` propagator `exp(-i H)` (Nielsen–Chuang eq. 2.91).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Problem 4.3(1).

This is the full content of the claim that `H = i ln(U)` is Hermitian with eigenvalues between
`0` and `2π`: choosing the `[0, 2π)`-branch of `ln`, the generator's spectrum lands in `[0, 2π]`.
-/
theorem Evolution.exists_hamiltonian_generator_spectrum_Icc (U : Evolution S) :
    ∃ H : Observable S, U = H.propagator 1 0 1 ∧
      spectrum ℂ H.op ⊆ Complex.ofReal '' Set.Icc 0 (2 * Real.pi) := sorry

end AxQM
