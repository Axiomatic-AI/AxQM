/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschGateDensity
import AxQM.Basic.API.ControlledUnitary

/-!
# AxQM.Basic.API — the Deutsch target gate `iR_x(θ)`

The single-qubit gate underlying Nielsen & Chuang, Exercise 4.44. The three-qubit
Deutsch gate is `G = C²(iR_x(πα))`: the doubly-controlled application of the operation `iR_x(θ)` to
the target qubit. This file packages that operation as a `qubit` `Evolution`.

## Main declarations
* `iRxGate θ` — the **Deutsch target gate** `iR_x(θ) = i · R_x(θ)` as an `Evolution qubit`, its
  operator the concrete matrix `Concrete.iRxMat θ` promoted through `Matrix.toEuclideanCLM`; the
  `Evolution` unitarity obligation is transported from `Concrete.iRxMat_mem_unitaryGroup`.
-/

noncomputable section

namespace AxQM

/-- The **Deutsch target gate** `iR_x(θ) = i · R_x(θ)` as a closed-system evolution of the
`qubit`. -/
def iRxGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.iRxMat θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      (Concrete.iRxMat_mem_unitaryGroup θ)

end AxQM
