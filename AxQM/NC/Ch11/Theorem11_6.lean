/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Nielsen & Chuang, Theorem 11.6 (Fannes' inequality)

*(N&C p. 512.)*

Fannes' inequality: bound on |S(rho)-S(sigma)| by trace distance and dimension.

* `abs_vonNeumannEntropy_sub_le_fannes` — the main bound (N&C eq. (11.44)): `|S(ρ) − S(σ)| ≤ T · log
  d + η(T)`, under the hypothesis `T ≤ 1/e`;
* `abs_vonNeumannEntropy_sub_le_fannes_weak` — the weaker unconditional bound (N&C eq. (11.45)):
  `|S(ρ) − S(σ)| ≤ T · log d + 1/e`, with the `T ≤ 1/e` restriction removed.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- **Fannes' inequality** (Nielsen & Chuang, Theorem 11.6, eq. (11.44)). For states `ρ, σ` of a
quantum system `S` whose trace distance satisfies `2·D(ρ, σ) ≤ 1/e`, the von Neumann entropies
differ by at most

`|S(ρ) − S(σ)| ≤ 2·D(ρ, σ) · log d + η(2·D(ρ, σ))`,

where `d = S.dim` is the dimension of the state space and `η = Real.negMulLog`. Here
`2·D(ρ, σ) = ‖ρ.op − σ.op‖₁` is N&C's trace-distance `T`.
-/
theorem State.abs_vonNeumannEntropy_sub_le_fannes (ρ σ : State S)
    (hT : 2 * ρ.traceDistance σ ≤ Real.exp (-1)) :
    |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      ≤ 2 * ρ.traceDistance σ * Real.log (S.dim : ℝ)
        + Real.negMulLog (2 * ρ.traceDistance σ) := sorry

/-- **Weaker (unconditional) Fannes' inequality** (Nielsen & Chuang, Theorem 11.6, eq. (11.45)).
Dropping the `T ≤ 1/e` restriction, for *any* states `ρ, σ` of a quantum system `S`,

`|S(ρ) − S(σ)| ≤ 2·D(ρ, σ) · log d + 1/e`,

where `d = S.dim`, `1/e = Real.exp (-1)`, and `2·D(ρ, σ) = ‖ρ.op − σ.op‖₁` is N&C's
trace-distance `T`. The bound is genuinely weaker than (11.44) but holds with no hypothesis on the
trace distance.
-/
theorem State.abs_vonNeumannEntropy_sub_le_fannes_weak (ρ σ : State S) :
    |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      ≤ 2 * ρ.traceDistance σ * Real.log (S.dim : ℝ) + Real.exp (-1) := sorry

end AxQM
