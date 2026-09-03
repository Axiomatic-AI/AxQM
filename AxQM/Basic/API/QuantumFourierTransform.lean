/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qudit
import AxQM.Concrete.QuantumFourierTransform
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Basic.API — the quantum Fourier transform as a unitary evolution

The physics **wrapper** promoting the concrete `d`-dimensional quantum Fourier transform matrix
`Concrete.qftMatrix d` (Nielsen & Chuang eq. 5.2, `Fₖⱼ = (1/√d)·e^{2πijk/d}`) to a genuine
unitary `Evolution` of the qudit register `qudit d`, together with its action on
computational-basis states.

## Main declarations
* `qftEvolution d` — the **QFT as a unitary `Evolution (qudit d)`**, whose operator is the concrete
  matrix promoted through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`. Unitarity is
  transported from `Concrete.qftMatrix_mem_unitaryGroup` by `Unitary.map_mem`. That this typechecks
  as an `Evolution` is the content of N&C's remark that the QFT is unitary, and so implementable
  as the dynamics of a quantum computer.
-/

noncomputable section

namespace AxQM

open AxQM.Concrete

/-- The **quantum Fourier transform on `qudit d`** as a unitary `Evolution` (Nielsen & Chuang eq.
5.2). This is the "dynamics for a quantum computer" realizing the transform. -/
def qftEvolution (d : ℕ) [NeZero d] : Evolution (qudit d) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) (qftMatrix_mem_unitaryGroup d)

end AxQM
