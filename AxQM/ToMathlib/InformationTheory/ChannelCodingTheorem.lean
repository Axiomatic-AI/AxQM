/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.NoisyChannel
public import AxQM.ToMathlib.InformationTheory.TypicalSequence

/-!
# Shannon's noisy channel coding theorem

**Shannon's noisy channel coding theorem** (Nielsen & Chuang, Theorem 12.7; Cover–Thomas,
Theorem 7.7.1): the *operational* capacity `C(N)` of a discrete memoryless channel `q` equals
its *information* capacity `max_{p(x)} H(X : Y)`.

## Main declarations

* `Real.channelOpCapacity_eq_channelCapacity_div` — **Shannon's noisy channel coding theorem**:
  `channelOpCapacity q = channelCapacity q / log 2`, i.e. `C(N) = max_{p(x)} H(X : Y)`.
-/

@[expose] public section

open Finset Filter Topology

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Shannon's noisy channel coding theorem** (Nielsen & Chuang, Theorem 12.7, eq. (12.67)): the
operational capacity `C(N)` of a discrete memoryless channel equals its information capacity
`max_{p(x)} H(X : Y)`,

`channelOpCapacity q = channelCapacity q / log 2`.
-/
theorem channelOpCapacity_eq_channelCapacity_div [Nonempty ι] [Nonempty κ] {q : ι → κ → ℝ}
    (hN : IsChannel q) : channelOpCapacity q = channelCapacity q / Real.log 2 := sorry

end Real
