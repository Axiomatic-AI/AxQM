/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ApproxError
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.QftApproxEvolution
import AxQM.Concrete.QftGateCount

/-!
# Nielsen & Chuang, Exercise 5.6 — the approximate quantum Fourier transform

*(N&C p. 221.)*

Approximate QFT: with R_k precision 1/p(n), error E(U,V)=max||(U-V)|psi>|| is Theta(n^2/p(n)).

* `qftApprox_gateError_div_mem_Icc`
-/

open scoped InnerProductSpace

namespace AxQM

open Concrete

/-- **Nielsen & Chuang, Exercise 5.6 — the `Θ(n²/p(n))` scaling of the approximate-QFT error (the
exercise's conclusion).** With each controlled-`Rₖ` gate implemented to precision `Δ = 1/p(n)`
(precision denominator `p`, `0 ≤ p(n)`), the error of the imperfect transform `V =
qftApproxEvolution n (1/p(n))` — the QFT N&C describes — is pinned on both sides:

`qftControlledRkCount n / p(n) / π ≤ E(U, V) ≤ qftControlledRkCount n / p(n)`,

in the small-error regime `qftControlledRkCount n / p(n) ≤ π`. The two bounds are
`qftControlledRkCount n / p(n) = n(n-1)/(2·p(n))` up to the constant factor `π`, and
`qftControlledRkCount n / p(n) = Θ(n²/p(n))`, so `E(U, V) = Θ(n²/p(n))` — polynomial precision
`1/p(n)` in each gate yields error scaling as `Θ(n²/p(n))`.
-/
theorem qftApprox_gateError_div_mem_Icc (n : ℕ) (p : ℕ → ℝ) (hp : 0 ≤ p n)
    (hreg : (qftControlledRkCount n : ℝ) / p n ≤ Real.pi) :
    (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n (1 / p n)) ∈
      Set.Icc ((qftControlledRkCount n : ℝ) / p n / Real.pi) ((qftControlledRkCount n : ℝ) / p n) :=
        sorry

end AxQM
