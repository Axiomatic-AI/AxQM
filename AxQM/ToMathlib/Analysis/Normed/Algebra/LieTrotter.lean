/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Lie–Trotter product formula

Let `𝔸` be a Banach algebra (a complete normed `ℝ`-algebra with `‖1‖ = 1`) and `x y : 𝔸`. This file
states the **Lie product formula**, also known as the **Trotter product formula**.

## Main results

* `NormedSpace.tendsto_pow_exp_smul_mul_exp_smul`: the Lie–Trotter product formula.
-/

@[expose] public section

open Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

namespace NormedSpace

variable [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The **explicit numerical Lie–Trotter constant** `2e + e²·eᵉ`, i.e.
`2·Real.exp 1 + Real.exp 1 ^ 2 · Real.exp (Real.exp 1)`. It is the numerical part of Nielsen &
Chuang, *Quantum Computation and Quantum Information*, Problem 4.3(6)'s `O(4ⁿ)` Trotter
constant. -/
noncomputable def trotterProductConst : ℝ :=
  2 * Real.exp 1 + Real.exp 1 ^ 2 * Real.exp (Real.exp 1)

/-- The Lie–Trotter product-formula constant `trotterProductConst` is nonnegative. -/
theorem trotterProductConst_nonneg : 0 ≤ trotterProductConst := by
  unfold trotterProductConst; positivity

/-- **The Lie product formula** (a.k.a. the **Trotter product formula**; Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Theorem 4.3). In a Banach algebra `𝔸`, for any `x y : 𝔸`,
`lim (exp(x/n) exp(y/n))ⁿ = exp(x + y)`, i.e. `Tendsto (fun n => (exp (n⁻¹ • x) * exp (n⁻¹ • y))
^ n) atTop (𝓝 (exp (x + y)))`. This holds even when `x` and `y` do **not** commute.
-/
theorem tendsto_pow_exp_smul_mul_exp_smul (x y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n) atTop
      (𝓝 (exp (x + y))) := sorry

end NormedSpace
