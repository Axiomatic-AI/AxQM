/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ProductStateCode
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.Basic.PiTensor
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# The product-state capacity `C⁽¹⁾(E)` of a noisy quantum channel (N&C §12.3.2)

This file defines the **product-state capacity** `C⁽¹⁾(E)` of a trace-preserving quantum operation
`E` — the quantity on the *right-hand side* of the Holevo–Schumacher–Westmoreland (HSW) theorem
(Nielsen & Chuang, Theorem 12.8, `χ(E) = C⁽¹⁾(E)`). It is the quantum analogue of Shannon's
operational channel capacity `C(N)` (N&C p. 552): the supremum of the rates at which Alice can
reliably send classical information to Bob using **product-state** codewords through the memoryless
channel `E`.

## Main definitions and results

* `AxQM.IsProductStateAchievableRate` — achievability of a rate `R` (N&C p. 552).
* `AxQM.productStateCapacity` — the product-state capacity `C⁽¹⁾(E)`.
-/

open ContinuousLinearMap InnerProductSpace Filter Topology
open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A rate `R` (in **nats** per channel use) is **achievable** for the memoryless channel `E` when
there is a family of product-state codes `codeₙ : ProductStateCode E n ⌈exp (n · R)⌉₊`, one for each
block length `n`, whose maximum error probability `maxError` tends to `0` as `n → ∞` (Nielsen &
Chuang, p. 552, for the quantum product-state model). The message count `⌈exp (n · R)⌉₊` is at least
`eⁿᴿ`, i.e. a rate of `R` nats per use over `n` uses — the natural-log analogue of N&C's
`2ⁿᴿ`. -/
def IsProductStateAchievableRate (E : State S → State S) (R : ℝ) : Prop :=
  ∃ code : (n : ℕ) → ProductStateCode E n ⌈Real.exp ((n : ℝ) * R)⌉₊,
    Tendsto (fun n => (code n).maxError) atTop (𝓝 0)

/-- The **product-state capacity** `C⁽¹⁾(E)` of the channel `E` (Nielsen & Chuang §12.3.2): the
supremum of all achievable rates for communication using product-state inputs. -/
def productStateCapacity (E : State S → State S) : ℝ :=
  sSup {R | IsProductStateAchievableRate E R}

end AxQM
