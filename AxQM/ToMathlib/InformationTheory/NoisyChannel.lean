/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.MutualInformationMap
public import AxQM.ToMathlib.Analysis.SpecialFunctions.ConditionalEntropyChain
public import AxQM.ToMathlib.Analysis.SpecialFunctions.DataProcessingInequality

/-!
# Discrete memoryless channels and the information capacity

For finite input and output alphabets `ι`, `κ` a **discrete memoryless channel** (Nielsen &
Chuang, *Quantum Computation and Quantum Information*, p. 551) is a family of conditional
probabilities `q : ι → κ → ℝ`, `q x y = p(y | x)`, satisfying `q x y ≥ 0` and `∑ y, q x y = 1`
for every input `x` (`Real.IsChannel`). Fed an input distribution `p : ι → ℝ` for a random
variable `X`, the channel produces the joint input–output law
`Real.channelJoint q p (x, y) = p x · q x y` of `(X, Y)`.

## Main declarations

* `Real.IsChannel` — a conditional distribution `q : ι → κ → ℝ` is a channel.
* `Real.channelJoint` — the induced joint distribution.
* `Real.channelMutualInfo` — `H(X : Y)` for a given input distribution.
* `Real.channelCapacity` — the information capacity `max_{p(x)} H(X : Y)`.
* `Real.ChannelCode` — a length-`n`, `M`-message block code (encoder `Cₙ` and decoder `Dₙ`).
* `Real.ChannelCode.maxErrorProb` — the block error probability `max_m p(Dₙ(Y) ≠ m | X = Cₙ(m))`
  (N&C eq. (12.66)).
* `Real.IsAchievableRate`, `Real.channelOpCapacity` — achievable rates and the operational capacity
  `C(N)`, the supremum of achievable rates.
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A **discrete memoryless channel** with input alphabet `ι` and output alphabet `κ`: a family of
conditional probabilities `q x y = p(y | x)` that is nonnegative and normalized over the output for
each input (Nielsen & Chuang, p. 551, eqs. (12.64)–(12.65)). -/
structure IsChannel (q : ι → κ → ℝ) : Prop where
  /-- Conditional probabilities are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ q x y
  /-- For each input the conditional distribution over outputs sums to one. -/
  row_sum : ∀ x, ∑ y, q x y = 1

/-- The **joint input–output distribution** `p_{XY}(x, y) = p(x) q(y | x)` of the input random
variable `X` and the channel output `Y`. -/
noncomputable def channelJoint (q : ι → κ → ℝ) (p : ι → ℝ) : ι × κ → ℝ :=
  fun xy => p xy.1 * q xy.1 xy.2

/-- The **channel mutual information** `H(X : Y)` between a channel `q`'s input `X`, distributed as
`p`, and its output `Y`: the mutual information of the joint input–output law. -/
noncomputable def channelMutualInfo (q : ι → κ → ℝ) (p : ι → ℝ) : ℝ :=
  mutualInfo (channelJoint q p)

/-- The **information capacity** of a channel `q`: the maximum of the mutual information `H(X : Y)`
over all input distributions `p`, i.e. the right-hand side `max_{p(x)} H(X : Y)` of Shannon's noisy
channel coding theorem (Nielsen & Chuang Theorem 12.7, eq. (12.67)). -/
noncomputable def channelCapacity (q : ι → κ → ℝ) : ℝ :=
  sSup (channelMutualInfo q '' stdSimplex ℝ ι)

section OperationalCapacity
open Finset Filter Topology

variable {n M : ℕ}

/-- A **block code** for `n` uses of a channel with input alphabet `ι`, output alphabet `κ` and `M`
messages (Nielsen & Chuang, p. 551). The intended dependence of the message count on the rate
`R` is `M = ⌈2 ^ (n R)⌉`. -/
structure ChannelCode (ι κ : Type*) (n M : ℕ) where
  /-- The encoding map `Cₙ`: each message is assigned an input codeword of length `n`. -/
  encode : Fin M → (Fin n → ι)
  /-- The decoding map `Dₙ`: each length-`n` output string is decoded to a message. -/
  decode : (Fin n → κ) → Fin M

/-- The **memoryless `n`-use transition probability** `p(y | x) = ∏ⱼ q(yⱼ | xⱼ)` of receiving the
output string `y : Fin n → κ` given the input string `x : Fin n → ι`, for a channel `q` used `n`
times. -/
noncomputable def channelSeqProb (q : ι → κ → ℝ) (x : Fin n → ι) (y : Fin n → κ) : ℝ :=
  ∏ j, q (x j) (y j)

/-- The **conditional block-error probability** for message `m` under channel `q`. -/
noncomputable def ChannelCode.condErrorProb (q : ι → κ → ℝ) (code : ChannelCode ι κ n M)
    (m : Fin M) : ℝ :=
  ∑ y ∈ univ.filter (fun y => code.decode y ≠ m), channelSeqProb q (code.encode m) y

/-- The **block error probability** of a code (Nielsen & Chuang, eq. (12.66)):
`p(Cₙ, Dₙ) = max_m p(Dₙ(Y) ≠ m | X = Cₙ(m))`, the maximum of the conditional error probability over
all messages. (For an empty message set the supremum is `0`.) -/
noncomputable def ChannelCode.maxErrorProb (q : ι → κ → ℝ) (code : ChannelCode ι κ n M) : ℝ :=
  ⨆ m, code.condErrorProb q m

/-- A rate `R` (in bits) is **achievable** for a channel `q` when there is a family of block codes
`codeₙ : ChannelCode ι κ n ⌈2 ^ (n R)⌉`, one per block length `n`, whose block error probability
`maxErrorProb` tends to `0` as `n → ∞` (Nielsen & Chuang, p. 552). The message count
`⌈exp (n · R · log 2)⌉₊` is `⌈2 ^ (n R)⌉` — at least `2 ^ (n R)` messages, corresponding to a rate
of `R` bits per channel use over `n` uses. -/
def IsAchievableRate (q : ι → κ → ℝ) (R : ℝ) : Prop :=
  ∃ code : (n : ℕ) → ChannelCode ι κ n ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊,
    Tendsto (fun n => (code n).maxErrorProb q) atTop (𝓝 0)

/-- The **operational capacity** `C(N)` of a channel `q`: the supremum of all achievable rates
(Nielsen & Chuang, p. 552). Shannon's noisy channel coding theorem identifies this
with the information capacity `channelCapacity q = max_{p(x)} H(X : Y)`. -/
noncomputable def channelOpCapacity (q : ι → κ → ℝ) : ℝ :=
  sSup {R | IsAchievableRate q R}

end OperationalCapacity

end Real
