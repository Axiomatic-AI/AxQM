/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BitOracleQueryCircuit
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl
import AxQM.Basic.API.ProjectiveMeasurement
import AxQM.Concrete.OrPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# AxQM.Basic.API — the zero-error query lower bound (method of polynomials)

The **query lower bound** Nielsen & Chuang's Exercise 6.20 asks for: any zero-error `T`-query
circuit computing OR needs `T ≥ N`.

## Main declarations

* `QuantumQueryProblem.measurement` — the projective computational-basis measurement
  `Measurement.ofOrthonormalBasis prob.basis`, with outcome type `σ × Bool × ω`.
-/

open scoped InnerProductSpace
open MvPolynomial AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- **The computational-basis measurement** of the query register: the projective `Measurement` in
the basis `|i,b,j⟩`, outcome type `σ × Bool × ω`. Its outcome is N&C's step-4 read-out of the
whole register, from which a classical function decodes the algorithm's answer (`0`, `1`, or
inconclusive). -/
def measurement : Measurement (σ × Bool × ω) S := Measurement.ofOrthonormalBasis prob.basis

end QuantumQueryProblem

end AxQM
