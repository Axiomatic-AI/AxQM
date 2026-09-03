/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import AxQM.ToMathlib.Analysis.Matrix.HilbertSchmidt

/-!
# Concrete: real-parameter count of an `n`-qubit density matrix (N&C Ex 4.46)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.46 (p. 205).
-/

namespace AxQM.Concrete

noncomputable section

/-- The (real) trace as a real-linear functional on the Hermitian matrices, `s ↦ Re (tr s)`.
Since a Hermitian matrix has real trace this records the full trace, and unit trace is the single
linear constraint `realTraceOnSelfAdjoint = 1` cutting density matrices out of the Hermitian
matrices. -/
def realTraceOnSelfAdjoint (d : ℕ) :
    selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ :=
  Complex.reLm ∘ₗ (Matrix.traceLinearMap (Fin d) ℝ ℂ) ∘ₗ
    (selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)).subtype

/-- The **traceless Hermitian** `d × d` matrices: the kernel of the real trace functional on the
Hermitian matrices. This is the "generalized Bloch vector" space — a density matrix is
`ρ = I/d + T` for a unique `T` in this space, so it parametrizes the density matrices. -/
def tracelessSelfAdjoint (d : ℕ) :
    Submodule ℝ (selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) :=
  LinearMap.ker (realTraceOnSelfAdjoint d)

/-- **Nielsen & Chuang, Exercise 4.46.** Describing an `n`-qubit density matrix requires `4ⁿ − 1`
independent real numbers: the traceless Hermitian `2ⁿ × 2ⁿ` matrices — the parameter space of
`n`-qubit density matrices — have real dimension `4ⁿ − 1`. -/
theorem finrank_tracelessSelfAdjoint_matrix_two_pow (n : ℕ) :
    Module.finrank ℝ (tracelessSelfAdjoint (2 ^ n)) = 4 ^ n - 1 := sorry

end

end AxQM.Concrete
