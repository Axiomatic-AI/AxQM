/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Concrete: the integer value of a big-endian bit-string

The classical index arithmetic behind Nielsen & Chuang's phase-estimation register (§5.2,
Exercise 5.7). A `t`-qubit computational-basis state `|j⟩ = |j₁ j₂ … j_t⟩` of the first register
carries the integer `j = ∑ₛ jₛ · 2^{t−s}` — the binary number with `j₁` the *most*-significant bit.
`bitsToNat` is that value function on a bit-string `b : Fin t → Fin 2`, defined by the
most-significant-bit-first recursion `bitsToNat (t+1) b = b₀ · 2ᵗ + bitsToNat t (tail b)`.
-/

namespace AxQM.Concrete

/-- **The integer value of a big-endian bit-string** `b : Fin t → Fin 2`, i.e. the binary number
`b₀ b₁ … b_{t-1}` with `b₀` the *most*-significant bit: `bitsToNat t b = ∑ₛ bₛ · 2^{t-1-s}`. Defined
by the most-significant-bit-first recursion, so that peeling the leading bit gives
`bitsToNat (t+1) b = b₀ · 2ᵗ + bitsToNat t (Fin.tail b)`. -/
def bitsToNat : (t : ℕ) → (Fin t → Fin 2) → ℕ
  | 0, _ => 0
  | (t + 1), b => (b 0 : ℕ) * 2 ^ t + bitsToNat t (Fin.tail b)

end AxQM.Concrete
