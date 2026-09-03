/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import AxQM.ToMathlib.Analysis.InnerProductSpace.PolarUnitary

/-!
# Trace-norm duality with unitaries (Nielsen & Chuang, Lemma 9.5)

For an operator `A` on a finite-dimensional inner product space `E` and a unitary `U`,
Nielsen & Chuang, *Quantum Computation and Quantum Information*, Lemma 9.5 (p. 410) states that
`‖A‖₁` is the greatest value of `|tr (A U)|` over unitaries `U`.

## Main results

* `ContinuousLinearMap.isGreatest_norm_trace_mul_unitary` — `‖A‖₁` is the greatest value of
  `|tr (A U)|` over unitaries `U`.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- **Nielsen & Chuang, Lemma 9.5** (bundled form): the trace norm `‖A‖₁ = tr |A|` is the *greatest*
value of `|tr (A U)|` over all unitaries `U`. -/
theorem isGreatest_norm_trace_mul_unitary (A : E →L[𝕜] E) :
    IsGreatest {r : ℝ | ∃ U ∈ unitary (E →L[𝕜] E), r = ‖LinearMap.trace 𝕜 E ↑(A * U)‖}
      A.traceNorm := sorry

end ContinuousLinearMap
