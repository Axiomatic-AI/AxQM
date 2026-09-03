/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.StateMajorization
import AxQM.Basic.Composite
import AxQM.Basic.API.GeneralizedDepolarizingChannel
import AxQM.Concrete.EntanglementCatalysis
import AxQM.ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropy

/-!
# AxQM.Basic.API — reduced states of the entanglement-catalysis example

The reduced density operators of the three bipartite pure states of Nielsen & Chuang,
Exercise 12.21 (entanglement catalysis), as diagonal `State`s on qudits carrying the
squared-Schmidt spectra.

## Main definitions

* `catalysisStatePsi`, `catalysisStatePhi` : `State (qudit 4)`, `catalysisStateCat` : `State
  (qudit 2)` — the reduced states, diagonal in the computational basis with spectra `λ_ψ`, `λ_φ`,
  `λ_c`.
-/

open Finset AxQM.Concrete

namespace AxQM

/-- The reduced density operator of the source state `|ψ⟩ = √0.4|00⟩ + √0.4|11⟩ + √0.1|22⟩ +
√0.1|33⟩` of the catalysis example: the diagonal state on `qudit 4` with the
squared-Schmidt spectrum `λ_ψ = (0.4, 0.4, 0.1, 0.1)`. -/
noncomputable def catalysisStatePsi : State (qudit 4) where
  op := (quditOrthonormalBasis 4).diagonalOperator fun i => (catalysisPsiSpec i : ℂ)
  isDensity := (quditOrthonormalBasis 4).diagonalOperator_isDensityOp
    catalysisPsiSpec_nonneg catalysisPsiSpec_sum_eq_one

/-- The reduced density operator of the target state `|φ⟩ = √0.5|00⟩ + √0.25|11⟩ + √0.25|22⟩` of the
catalysis example: the diagonal state on `qudit 4` with the squared-Schmidt
spectrum `λ_φ = (0.5, 0.25, 0.25, 0)`. -/
noncomputable def catalysisStatePhi : State (qudit 4) where
  op := (quditOrthonormalBasis 4).diagonalOperator fun i => (catalysisPhiSpec i : ℂ)
  isDensity := (quditOrthonormalBasis 4).diagonalOperator_isDensityOp
    catalysisPhiSpec_nonneg catalysisPhiSpec_sum_eq_one

/-- The reduced density operator of the catalyst `|c⟩ = √0.6|00⟩ + √0.4|11⟩`:
the diagonal state on `qudit 2` with spectrum `λ_c = (0.6, 0.4)`. -/
noncomputable def catalysisStateCat : State (qudit 2) where
  op := (quditOrthonormalBasis 2).diagonalOperator fun i => (catalysisCatSpec i : ℂ)
  isDensity := (quditOrthonormalBasis 2).diagonalOperator_isDensityOp
    catalysisCatSpec_nonneg catalysisCatSpec_sum_eq_one

end AxQM
