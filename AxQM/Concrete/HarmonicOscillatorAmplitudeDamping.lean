/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Concrete: amplitude damping of a harmonic oscillator (N&C, Exercise 8.21)

The operation elements of the **amplitude-damping quantum operation of a harmonic oscillator**
(Nielsen & Chuang, Exercise 8.21, p. 381).

## The exercise

1. derive the operation elements `Eₖ` (eq. 8.110) from `U`, and
2. show the `Eₖ` define a *trace-preserving* quantum operation, i.e. `Σₖ Eₖ† Eₖ = I`.

## Contents

* `fockDampingProbCoef` — `C(n,k) (1-γ)^{n-k} γ^k`, the probability of losing `k` quanta from
  level `n`.
* `fockDampingAmp` — `√(fockDampingProbCoef)`, the amplitude in eq. 8.110.
* `fockDampingKraus` — the operation element `Eₖ` of eq. 8.110, as a `Matrix ℕ ℕ ℂ`.
* `fockDampingKraus_completeness` — **Exercise 8.21(2):** the trace-preservation / completeness
  relation `Σₖ Eₖ† Eₖ = I`, stated entrywise.
-/

namespace AxQM.Concrete

open Matrix
open scoped BigOperators

/-- The **probability of losing `k` quanta from the `n`-quantum level**, `C(n,k) (1-γ)^{n-k} γ^k`.
-/
noncomputable def fockDampingProbCoef (γ : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (1 - γ) ^ (n - k) * γ ^ k

/-- The **amplitude** `√( C(n,k) (1-γ)^{n-k} γ^k )` of the operation element `Eₖ` on `|n⟩`
(eq. 8.110). -/
noncomputable def fockDampingAmp (γ : ℝ) (n k : ℕ) : ℝ :=
  Real.sqrt (fockDampingProbCoef γ n k)

/-- The **operation element** `Eₖ` of amplitude damping (eq. 8.110), as an infinite matrix over the
number-state index `ℕ`: `Eₖ = Σₙ √( C(n,k) (1-γ)^{n-k} γ^k ) |n-k⟩⟨n|`. -/
noncomputable def fockDampingKraus (γ : ℝ) (k : ℕ) : Matrix ℕ ℕ ℂ :=
  fun r c => if r + k = c then (fockDampingAmp γ c k : ℂ) else 0

/-- **Exercise 8.21(2): the operation elements define a trace-preserving quantum operation.** The
completeness relation `Σₖ Eₖ† Eₖ = I`, stated entrywise over the number-state index `ℕ`: for all
`a b : ℕ`,
`∑ᶠ k, ∑ᶠ j, (Eₖ)ᴴ a j · (Eₖ) j b = I_{ab}`,
where the inner `∑ᶠ j` is the `(a,b)` entry of `Eₖ† Eₖ`. -/
theorem fockDampingKraus_completeness {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a b : ℕ) :
    (∑ᶠ k, ∑ᶠ j, (fockDampingKraus γ k)ᴴ a j * fockDampingKraus γ k j b)
      = (1 : Matrix ℕ ℕ ℂ) a b := sorry

end AxQM.Concrete
