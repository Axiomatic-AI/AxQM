/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.Normed.Algebra.LieTrotter

/-!
# Small-parameter Taylor estimates for exponential splittings

Let `𝔸` be a Banach algebra (a complete normed `ℝ`-algebra with `‖1‖ = 1`) and `x y : 𝔸`. This
file records the low-order `t → 0` (Taylor) error estimates for splitting the exponential of a sum
into a product of exponentials, phrased with `Asymptotics.IsBigO`: the statement
`f =O[𝓝 0] (fun t => tⁿ)` is exactly "`f t = O(tⁿ)` as `t → 0`", i.e. a constant `C` and a
neighbourhood of `0` on which `‖f t‖ ≤ C·|t|ⁿ`. The filter is the two-sided `𝓝 0`, so these are the
full-strength claims, not weakenings to `t ≥ 0`.

## Main results

* `NormedSpace.isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul`: the **first-order Lie–Trotter
  splitting error** `exp(t•(x+y)) - exp(t•x) exp(t•y) =O[𝓝 0] (fun t => t²)`, i.e. N&C (4.103).

* `NormedSpace.isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul_mul_exp_lie`: the **second-order
  Baker–Campbell–Hausdorff formula** `exp(t•(x+y)) - exp(t•x) exp(t•y) exp(-½t²•⁅x, y⁆) =O[𝓝 0]
  (fun t => t³)`, i.e. N&C (4.105).

* `NormedSpace.isBigO_exp_smul_add_sub_exp_half_smul_mul_exp_smul_mul_exp_half_smul`: the
  **symmetric (Strang) splitting**
  `exp(t•(x+y)) - exp((t/2)•x) exp(t•y) exp((t/2)•x) =O[𝓝 0] (fun t => t³)`, i.e. N&C (4.104).
-/

@[expose] public section

open Asymptotics Filter Topology

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **First-order error of the Lie–Trotter splitting of two exponentials.** In a Banach algebra, as
`t → 0`,
`exp(t•(x+y)) - exp(t•x) exp(t•y) = O(t²)`,
so replacing `exp(t•(x+y))` by the ordered product `exp(t•x) exp(t•y)` incurs only a second-order
error, even when `x` and `y` do **not** commute.

This is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.49, equation
(4.103): with `x = i·A`, `y = i·B` it reads `e^{i(A+B)Δt} = e^{iAΔt} e^{iBΔt} + O(Δt²)`. -/
theorem isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul (x y : 𝔸) :
    (fun t : ℝ => exp (t • (x + y)) - exp (t • x) * exp (t • y)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := sorry

/-- **The second-order Baker–Campbell–Hausdorff formula.** In a Banach algebra, as `t → 0`,
`exp(t•(x+y)) - exp(t•x) exp(t•y) exp(-½t²•⁅x, y⁆) = O(t³)`, where `⁅x, y⁆ = xy - yx` is the
commutator. So the symmetric second-order correction that turns the naive splitting `exp(t•x)
exp(t•y)` into an `O(t³)` approximation of `exp(t•(x+y))` is exactly `exp(-½t²•⁅x, y⁆)`.

This is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.49, equation
(4.105): `e^{(A+B)Δt} = e^{AΔt} e^{BΔt} e^{-½[A,B]Δt²} + O(Δt³)`. The exponent `t²•(-½•⁅x, y⁆)`
of the third factor is `-½[x, y]Δt²`.
-/
theorem isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul_mul_exp_lie (x y : 𝔸) :
    (fun t : ℝ => exp (t • (x + y))
        - exp (t • x) * exp (t • y) * exp (t ^ 2 • ((-2⁻¹ : ℝ) • ⁅x, y⁆))) =O[𝓝 0]
      (fun t : ℝ => t ^ 3) := sorry

/-- **The symmetric (Strang) splitting.** In a Banach algebra, as `t → 0`, `exp(t•(x+y)) -
exp((t/2)•x) exp(t•y) exp((t/2)•x) = O(t³)`.

This is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.49, equation
(4.104).
-/
theorem isBigO_exp_smul_add_sub_exp_half_smul_mul_exp_smul_mul_exp_half_smul (x y : 𝔸) :
    (fun t : ℝ => exp (t • (x + y))
        - exp ((t / 2) • x) * exp (t • y) * exp ((t / 2) • x)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := sorry

end NormedSpace
