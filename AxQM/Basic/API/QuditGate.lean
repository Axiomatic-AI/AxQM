/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qudit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Basic.API — a unitary matrix as an `Evolution` gate on `qudit d`

Promotes a `d × d` unitary matrix to a closed-system `Evolution (qudit d)`. The register model of
Nielsen & Chuang's circuits is `qudit (2ⁿ)`, and many gates are naturally specified as concrete
`d × d` unitary matrices.
-/

open Matrix

noncomputable section

namespace AxQM

/-- The **unitary gate of a `d × d` unitary matrix** `U` (`hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ`)
as a closed-system `Evolution` of `qudit d`. -/
def quditGate {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Evolution (qudit d) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) U
  unitary := Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) hU

end AxQM
