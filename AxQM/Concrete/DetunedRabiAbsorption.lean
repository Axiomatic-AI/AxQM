/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# Concrete: absorption by a detuned two-level block

The closed-form matrix
exponential of the `2 × 2` Hamiltonian block
-/

namespace AxQM.Concrete

open NormedSpace Matrix

noncomputable section

open scoped Matrix.Norms.Operator

/-- The detuned two-level Hamiltonian block `M(δ, g) = [[-δ, g], [g, δ]]`: the one-excitation block
of the (non-resonant) Jaynes–Cummings Hamiltonian, with level splitting `2δ` and coupling `g`
(Nielsen & Chuang eq. (7.84)). -/
def detunedBlock (δ g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-δ : ℂ), (g : ℂ); (g : ℂ), (δ : ℂ)]

end

end AxQM.Concrete
