/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.NoisyChannel

/-!
# The erasure and binary symmetric channels, and their capacities

The **erasure channel** (Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise
12.9, p. 553) has two inputs `0, 1` and three outputs `0, 1, e`: with probability `1 - r` the input
is transmitted unchanged, and with probability `r` it is *erased* and replaced by the special symbol
`e`. We model it as `Real.erasureChannel r : Fin 2 → Option (Fin 2) → ℝ`, where the output type
`Option (Fin 2)` uses `none` for the erasure symbol `e` and `some z` for the transmitted bit `z`.

## Main declarations

* `Real.erasureChannel` — the erasure channel with erasure probability `r`.
* `Real.erasureChannel_channelCapacity` — the capacity is `(1 - r) · log 2`.
* `Real.bscChannel` — the binary symmetric channel with crossover probability `p`.
* `Real.erasureChannel_capacity_gt_bsc` — the erasure capacity exceeds the BSC capacity on
  `0 < p ≤ 1/2` (Exercise 12.9 (2)).
-/

@[expose] public section

namespace Real

/-- The **erasure channel** with erasure probability `r`: on input `x : Fin 2` it outputs the bit
`x` (i.e. `some x`) with probability `1 - r`, and the erasure symbol `e` (i.e. `none`) with
probability `r`. -/
def erasureChannel (r : ℝ) : Fin 2 → Option (Fin 2) → ℝ :=
  fun x y =>
    match y with
    | none => r
    | some z => if z = x then 1 - r else 0

/-- **Exercise 12.9 (1).** The capacity of the erasure channel with erasure probability `0 ≤ r ≤ 1`
is `(1 - r) · log 2` — Nielsen & Chuang's `1 - r`, measured in nats (their `1` is `log 2`). -/
theorem erasureChannel_channelCapacity {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    channelCapacity (erasureChannel r) = (1 - r) * Real.log 2 := sorry

/-- The **binary symmetric channel** with crossover probability `p` (Nielsen & Chuang, p. 552): on
input `x : Fin 2` it outputs `x` unchanged with probability `1 - p` and the flipped bit `1 - x` with
probability `p` (i.e. it outputs `y` with probability `p` when `y ≠ x`). -/
def bscChannel (p : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun x y => if y = x then 1 - p else p

/-- **Exercise 12.9 (2).** On the standard noise regime `0 < p ≤ 1/2`, the capacity of the erasure
channel exceeds the capacity of the binary symmetric channel with the *same* parameter `p`. The
unrestricted claim as printed is false, so the natural `0 < p ≤ 1/2` regime, where the binary
symmetric channel is conventionally defined (a crossover `p > 1/2` is relabelled to `1 - p`),
is required. -/
theorem erasureChannel_capacity_gt_bsc {p : ℝ} (h0 : 0 < p) (h1 : p ≤ 2⁻¹) :
    channelCapacity (bscChannel p) < channelCapacity (erasureChannel p) := sorry

/-- The **unrestricted** form of Exercise 12.9 (2) is *false*: `erasureChannel_capacity_gt_bsc`
genuinely needs its `0 < p ≤ 1/2` hypothesis. At `p = 1` the binary symmetric channel *always*
flips the bit and the erasure channel *always* erases, and there the erasure capacity is
*strictly smaller* than the BSC capacity — the exact reverse of the printed claim. -/
theorem channelCapacity_erasureChannel_lt_bscChannel_at_one :
    channelCapacity (erasureChannel 1) < channelCapacity (bscChannel 1) := sorry

end Real
