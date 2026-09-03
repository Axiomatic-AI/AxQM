/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.Coding.GilbertVarshamov
public import AxQM.ToMathlib.InformationTheory.Coding.DualCode

/-!
# The Gilbert–Varshamov existence bound for CSS quantum codes (combinatorial core)

The CSS (Calderbank–Shor–Steane) construction turns a *nested pair* of classical linear codes
`C₂ ⊆ C₁ ⊆ 𝔽₂ⁿ` in which **both `C₁` and `C₂⊥` correct `t` errors** into an `[n, k₁ - k₂]` quantum
code correcting `t` qubit errors (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
§10.4.2). Its **Gilbert–Varshamov bound** (N&C Problem 10.2, eq. (10.122)) asserts that such a pair
exists with rate `(k₁ - k₂)/n ≥ 1 - 2 H₂(2t/n)`.

## Main results

* `LinearCode.exists_nestedPair_correctsErrors_of_rate_le`: the rate form. For `4t ≤ n` and target
  CSS dimension `k` with `k + 4 ≤ n · (1 - 2 H₂(2t/n))`, there is a nested pair `C₂ ⊆ C₁` with both
  `C₁` and `C₂⊥` correcting `t` errors and `k + dim C₂ ≤ dim C₁` — the Gilbert–Varshamov rate
  `(dim C₁ - dim C₂)/n ≥ 1 - 2 H₂(2t/n)` of N&C (10.122)/(10.74).
-/

open Finset Matrix

public section

variable {n : ℕ}

namespace LinearCode

/-- **Gilbert–Varshamov bound for CSS codes, entropy (rate) form** (Nielsen & Chuang, Problem 10.2,
eqs. (10.122)/(10.74)). In the regime `4t ≤ n` (so the entropy argument `2t/n` lies in `[0, 1/2]`),
if the target CSS dimension `k` satisfies `k + 4 ≤ n · (1 - 2 H₂(2t/n))` — i.e.
`k / n ≥ 1 - 2 H₂(2t/n)` up to a vanishing additive constant, with `H₂ = Real.binEntropyBit` the
base-`2` binary entropy — then there is a nested pair of binary linear codes
`C₂ ⊆ C₁ ⊆ (Fin n → ZMod 2)` with

* `CorrectsErrors C₁ t` (i.e. `2t + 1 ≤ minDist C₁`);
* `CorrectsErrors (dual C₂) t` (i.e. `2t + 1 ≤ minDist C₂⊥`);
* `k + dim C₂ ≤ dim C₁`, i.e. the CSS code `CSS(C₁, C₂)` has dimension `dim C₁ - dim C₂ ≥ k`.

By the CSS construction of §10.4.2, such a pair yields an `[n, dim C₁ - dim C₂]` quantum code
correcting `t` qubit errors.
-/
theorem exists_nestedPair_correctsErrors_of_rate_le {n k t : ℕ} (h4t : 4 * t ≤ n)
    (hrate : (k : ℝ) + 4 ≤ n * (1 - 2 * Real.binEntropyBit (2 * t / n))) :
    ∃ C₁ C₂ : LinearCode (ZMod 2) (Fin n),
      C₂ ≤ C₁ ∧ CorrectsErrors C₁ t ∧ CorrectsErrors (dual C₂) t ∧
        k + Module.finrank (ZMod 2) C₂ ≤ Module.finrank (ZMod 2) C₁ := sorry

end LinearCode

end
