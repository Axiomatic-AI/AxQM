/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Concrete: the improved `O(L² log L log log L)` factoring cost (N&C Problem 5.4)

Nielsen & Chuang, Problem 5.4 (p. 244): the runtime bound `O(L³)` given for the factoring algorithm
is not tight; a better upper bound of `O(L² log L log log L)` operations can be achieved.
-/

namespace AxQM.Concrete

open Filter Asymptotics

/-- The Schönhage–Strassen fast-multiplication operation count `O(L log L log log L)` for
multiplying two `L`-bit integers — the per-multiplication cost that replaces the naive `O(L²)` in
the factoring algorithm (N&C Problem 5.4). -/
noncomputable def fastMulOpBound (L : ℕ) : ℝ :=
  (L : ℝ) * Real.log L * Real.log (Real.log L)

/-- The improved total operation-count bound `O(L² log L log log L)` for factoring an `L`-bit
integer, achieved by using fast (Schönhage–Strassen) multiplication in the modular exponentiation
step (N&C Problem 5.4): `L` modular multiplications, each of cost `fastMulOpBound L`. -/
noncomputable def factoringFastOpBound (L : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * Real.log L * Real.log (Real.log L)

/-- The number of modular multiplications performed by the Box 5.2 modular-exponentiation circuit on
a `t`-qubit exponent register (N&C p. 228): `t − 1` squarings to build `x, x², x⁴, …, x^{2^{t-1}}`
mod N by repeated squaring (stage 1), plus `t − 1` modular multiplications to form the product
`x^z = ∏_j x^{z_j 2^j}` mod N (stage 2). -/
def modExpMulCount (t : ℕ) : ℕ := (t - 1) + (t - 1)

/-- The exponent-register size `t = 2L + 1 + c` used by order-finding on an `L`-bit modulus (N&C
p. 227); `c = ⌈log(2 + 1/(2ε))⌉` is a fixed accuracy-dependent constant (independent of `L`). -/
def orderFindingRegisterSize (c L : ℕ) : ℕ := 2 * L + 1 + c

/-- The number of modular multiplications the order-finding modular-exponentiation circuit performs
when factoring an `L`-bit modulus, at accuracy constant `c`: `modExpMulCount` on the register size
`orderFindingRegisterSize c L`.  It equals `4L + 2c`. -/
def factoringModExpMulCount (c L : ℕ) : ℕ := modExpMulCount (orderFindingRegisterSize c L)

/-- **N&C Problem 5.4 — the improved bound is genuinely better than `O(L³)`.** `L² log L log log L =
o(L³)`: the improved factoring bound is asymptotically *strictly* smaller than the cubic bound
N&C says is "not tight". -/
theorem factoringFastOpBound_isLittleO_cubic :
    factoringFastOpBound =o[atTop] fun L : ℕ => (L : ℝ) ^ 3 := sorry

/-- An upper bound on the operations of the order-finding circuit *other than* the modular
exponentiation. For an `L`-bit modulus this is `(2L + 1 + c)²`, i.e. `Θ(L²)`, so it is dominated
by the improved modular-exponentiation bound. -/
def factoringQftGateBound (c L : ℕ) : ℕ := orderFindingRegisterSize c L ^ 2

/-- **N&C Problem 5.4 — the whole factoring algorithm achieves `O(L² log L log log L)`.**  On top of
the quantum circuit proper, N&C's resource summary (p. 232) counts a *further* `O(L³)` for the
continued-fractions recovery of the order and an `O(L²)` classical order→factor reduction;
Problem 5.4 asks to improve this whole count. The two arithmetic-bound parts share one
per-operation cost `mulCost` (one `O(L)`-bit multiply/divide): the modular exponentiation
(`factoringModExpMulCount c L` multiplications) and the continued-fractions post-processing
(`cfStepCount L` split-and-invert steps, `O(L)` by Box 5.3, `hCF`). With fast
(Schönhage–Strassen) multiplication (`hMul`) every arithmetic-bound part is `O(L² log L log log
L)`, so the whole algorithm is `O(L² log L log log L)` — Problem 5.4's bound for the algorithm
as a whole, not merely its dominant subroutine. -/
theorem factoringTotalOpCount_isBigO_of_fastMul (c : ℕ)
    {mulCost cfStepCount reductionCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fastMulOpBound)
    (hCF : cfStepCount =O[atTop] fun L : ℕ => (L : ℝ))
    (hRed : reductionCost =O[atTop] fun L : ℕ => (L : ℝ) ^ 2) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L + (factoringQftGateBound c L : ℝ)
        + cfStepCount L * mulCost L + reductionCost L) =O[atTop] factoringFastOpBound := sorry

end AxQM.Concrete
