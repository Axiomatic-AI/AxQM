/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.Basic.API.TensorPowState

/-!
# The product-state coding model for a noisy quantum channel (N&C §12.3.2)

This file sets up the operational model behind the **product-state capacity** `C⁽¹⁾(E)` of a
trace-preserving quantum operation `E`, the object on the right-hand side of the
Holevo–Schumacher–Westmoreland (HSW) theorem. It is the quantum
analogue of the classical noisy-channel coding setup (N&C §12.2.2): Alice encodes a message using a
**product state** of single-use channel inputs, Bob decodes the channel output with a measurement,
and the figures of merit are the resulting error probabilities.

## Main definitions and results

* `AxQM.ProductStateCode` — a product-state code (encoder + POVM decoder).
* `AxQM.ProductStateCode.outputCodeword` — the channel output `σ_M = ⊗ᵢ E(ρ_{Mᵢ})`.
* `AxQM.ProductStateCode.successProb` / `errorProb` — `tr(σ_M E_M)` and its
  complement `pᵉ_M = 1 − tr(σ_M E_M)`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A **product-state code** for a channel `E`, block length `n`, and message set `Fin K`
(Nielsen & Chuang §12.3.2). Alice's `encoder` sends each message to the `n` single-use input states
whose tensor product is the codeword; Bob's `decoder` is a measurement (POVM) on the `n`-fold output
system `S ^⊗ₛ n`, with outcome `some M` decoding to message `M` and `none` the inconclusive element
`E₀`. Codes are defined for an arbitrary state-map `E`; the trace-preserving hypothesis is imposed
downstream. -/
structure ProductStateCode (E : State S → State S) (n K : ℕ) where
  /-- The encoder: message `M ↦ (ρ_{M₁}, …, ρ_{Mₙ})`, the single-use inputs whose product
  `ρ_{M₁} ⊗ ⋯ ⊗ ρ_{Mₙ}` is Alice's codeword for `M`. -/
  encoder : Fin K → Fin n → State S
  /-- Bob's decoding measurement on the `n`-fold output system: outcome `some M` = "decoded `M`",
  outcome `none` = the extra inconclusive POVM element `E₀`. -/
  decoder : Measurement (Option (Fin K)) (S.tensorPow n)

namespace ProductStateCode

variable {E : State S → State S} {n K : ℕ}

/-- The **channel output for message `M`**, `σ_M = E⊗ⁿ(ρ_M) = E(ρ_{M₁}) ⊗ ⋯ ⊗ E(ρ_{Mₙ})`. Because
the channel is memoryless and the input codeword is a product state, `σ_M` is the product of the
single-use outputs `E(ρ_{Mᵢ})`. -/
def outputCodeword (c : ProductStateCode E n K) (m : Fin K) : State (S.tensorPow n) :=
  State.piTensor fun i => E (c.encoder m i)

/-- The **probability that Bob correctly decodes message `M`**, `tr(σ_M E_M)`: the Born probability
that the decoding measurement returns the outcome `some M` on the channel output `σ_M`. -/
def successProb (c : ProductStateCode E n K) (m : Fin K) : ℝ :=
  c.decoder.bornProb (c.outputCodeword m) (some m)

/-- The **error probability for message `M`**, `pᵉ_M = 1 − tr(σ_M E_M)` (Nielsen & Chuang, the
quantity just below eq. (12.71)): the probability Bob's decoding measurement does *not* return
`some M` on the channel output `σ_M`. -/
def errorProb (c : ProductStateCode E n K) (m : Fin K) : ℝ :=
  1 - c.successProb m

/-- The **maximum error probability** `max_M pᵉ_M` over all messages. -/
def maxError (c : ProductStateCode E n K) : ℝ :=
  ⨆ m, c.errorProb m

end ProductStateCode

end AxQM
