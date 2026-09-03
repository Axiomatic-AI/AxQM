/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.ApproxError
import AxQM.Concrete.QftGateCircuit
import AxQM.Concrete.QuantumFourierTransform
import Mathlib.Algebra.BigOperators.Field
import AxQM.Concrete.QftGateCircuitPerturbed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# AxQM.Basic.API — the approximate (imperfect) QFT as a unitary evolution

The physics **wrapper** promoting the concrete perturbed Figure 5.1 QFT circuit
`Concrete.qftGateCircuitPerturbed n Δ` — the ideal gate-level QFT with every controlled-`Rₖ`
performed to precision `Δ` — to a genuine unitary `Evolution` of
the `n`-qubit register `qudit (2ⁿ)`. This is the imperfect transform `V` whose distance from the
ideal QFT `U = qftEvolution (2ⁿ)` the faithful `Ω(n²/p(n))` half of Exercise 5.6 lower-bounds.

## Main declarations
* `qftApproxEvolution n Δ` — the **imperfect QFT as a unitary `Evolution (qudit (2ⁿ))`**, the ideal
  QFT with every controlled-`Rₖ` gate implemented to precision `Δ`. It is the concrete perturbed
  circuit matrix `Concrete.qftGateCircuitPerturbed n Δ` (unitary by
  `Concrete.qftGateCircuitPerturbed_mem_unitaryGroup`) promoted to an `Evolution` through the shared
  matrix-gate constructor `quditGate` — the `Δ`-perturbed twin of `qftEvolution (2ⁿ)`.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace AxQM

open AxQM.Concrete Matrix

/-- The **approximate (imperfect) quantum Fourier transform on `qudit (2ⁿ)`** as a unitary
`Evolution`: the ideal QFT with every controlled-`Rₖ` gate implemented to precision `Δ`. This is
the imperfect transform `V` of Exercise 5.6, the `Δ`-perturbed twin of `qftEvolution (2ⁿ)`. -/
def qftApproxEvolution (n : ℕ) (Δ : ℝ) : Evolution (qudit (2 ^ n)) :=
  quditGate (qftGateCircuitPerturbed_mem_unitaryGroup n Δ)

end AxQM
