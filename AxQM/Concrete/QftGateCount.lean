/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Concrete: the quantum-Fourier-transform gate count `n(n-1)/2 = Θ(n²)` (N&C Exercise 5.6)

The `n`-qubit quantum Fourier transform circuit (Nielsen & Chuang, Figure 5.1) applies, to qubit
`j` (counting `1 … n`), one Hadamard followed by controlled-`R₂ … R_{n-j+1}` phase rotations, i.e.
`n - j` controlled-`Rₖ` gates. The controlled-`Rₖ` gates are the only ones carrying a continuous
phase parameter, hence the only gates that must be implemented to finite **precision**; their total
number is `n(n-1)/2 = Θ(n²)`.
-/

namespace AxQM.Concrete

open Filter Asymptotics

/-- **The controlled-`Rₖ` gate count of the `n`-qubit QFT circuit** (Nielsen & Chuang, Figure 5.1):
`qftControlledRkCount n = n(n-1)/2`. Qubit `j` receives `n - j` controlled phase rotations, and
`∑_{j=1}^{n} (n - j) = n(n-1)/2`; these are the circuit's only gates carrying a continuous phase
parameter (the Hadamards and swaps are exact), hence the only ones implemented to finite precision
in Exercise 5.6. -/
def qftControlledRkCount (n : ℕ) : ℕ := n * (n - 1) / 2

/-- **The approximate-QFT error bound scales as `Θ(n²/p(n))`** (Nielsen & Chuang, Exercise 5.6). For
any precision denominator `p : ℕ → ℝ` (`Δ = 1/p(n)`), the guaranteed error bound `n(n-1)/(2·p(n)) =
qftControlledRkCount n / p n` — the imprecise-gate count times the per-gate precision — grows as
`Θ(n²/p(n))`. This is the scaling of the error *bound*. -/
theorem qftApproxErrorBound_isTheta (p : ℕ → ℝ) :
    (fun n : ℕ => (qftControlledRkCount n : ℝ) / p n)
      =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 2 / p n) := sorry

end AxQM.Concrete
