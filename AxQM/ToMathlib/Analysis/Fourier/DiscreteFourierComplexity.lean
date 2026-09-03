/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Operation counts of the discrete Fourier transform and the fast Fourier transform

This file develops the operation-count analysis underlying Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 5.3 (p. 221): computing the discrete Fourier
transform (DFT, N&C (5.1)) of a vector of `N = 2 ^ n` complex numbers by **direct evaluation**
costs `Θ(2 ^ (2 n))` elementary arithmetic operations, whereas the **fast Fourier transform**
(FFT) — the divide-and-conquer algorithm induced by the product form N&C (5.4) — reduces this to
`Θ(n · 2 ^ n)`.
-/

@[expose] public section

open Filter Asymptotics

namespace DiscreteFourier

/-- **Direct-evaluation operation count** of the discrete Fourier transform on `N = 2 ^ n` points.

The DFT is the matrix–vector product with the `N × N` Fourier matrix (N&C (5.1)). Evaluating all
`N` outputs directly, each as a sum of `N` products, uses `N ^ 2 = 4 ^ n` complex multiplications
and `N · (N − 1) = 2 ^ n · (2 ^ n − 1)` additions. -/
def directDftOpCount (n : ℕ) : ℕ := 4 ^ n + 2 ^ n * (2 ^ n - 1)

/-- **Fast Fourier transform operation count** on `N = 2 ^ n` points, as the divide-and-conquer
recurrence induced by the product form N&C (5.4): a size-`2 ^ (n+1)` transform is two
size-`2 ^ n` transforms (on even/odd inputs) plus a `2 ^ (n + 1)`-operation butterfly combine.
The `n = 0` (single point) transform costs nothing. -/
def fftOpCount : ℕ → ℕ
  | 0 => 0
  | (n + 1) => 2 * fftOpCount n + 2 ^ (n + 1)

/-- **Direct evaluation is `Θ(2 ^ (2 n))`** — the first claim of N&C Exercise 5.3. The direct DFT
operation count grows at the same rate as `2 ^ (2 n) = 4 ^ n = N ^ 2`. -/
theorem directDftOpCount_isTheta :
    (fun n => (directDftOpCount n : ℝ)) =Θ[atTop] fun (n : ℕ) => (2 : ℝ) ^ (2 * n) := sorry

/-- **The FFT is `Θ(n · 2 ^ n)`** — the second claim of N&C Exercise 5.3: the product form (5.4)
reduces the transform's cost to `Θ(n · 2 ^ n)`. -/
theorem fftOpCount_isTheta :
    (fun n => (fftOpCount n : ℝ)) =Θ[atTop] fun (n : ℕ) => (n : ℝ) * 2 ^ n := sorry

end DiscreteFourier
