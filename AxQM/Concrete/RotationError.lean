/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete: the gate-approximation error between two same-axis qubit rotations

## Main results (Nielsen & Chuang, Exercise 4.40)

* `rotAxis_opNorm_sub` — **eq. (4.77)**: `E(R_n̂(α), R_n̂(α+β)) = ‖1 − exp(iβ/2)‖`. Only the angle
  difference `β` matters, not the base angle `α`.
* `exists_pow_opNorm_sub_lt` — **eq. (4.76)** stated as an actual theorem: given that the angles
  `{kθ mod 4π}` approximate `α` arbitrarily well (the density hypothesis `hdense`, a genuine
  restriction — false, e.g., for `θ` a rational multiple of `2π`), for every `ε > 0` some iterate
  satisfies `‖R_n̂(α) − R_n̂(θ)^k‖ < ε`.
-/

namespace AxQM.Concrete

open ContinuousLinearMap

variable {n : Fin 3 → ℝ}

/-- The **qubit rotation operator** `R_n̂(θ)` as a continuous endomorphism of
`EuclideanSpace ℂ (Fin 2)`: the concrete `2 × 2` matrix `rotAxis n θ` promoted through the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM`. Naming it lets the gate-error statements below
refer to `R_n̂(θ)` as one operator rather than an inlined promotion. -/
noncomputable def rotAxisCLM (n : Fin 3 → ℝ) (θ : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (rotAxis n θ)

/-- **Nielsen & Chuang, Exercise 4.40, eq. (4.77).** The gate-approximation error
`E(R_n̂(α), R_n̂(α+β)) = ‖R_n̂(α) − R_n̂(α+β)‖` — the operator norm, i.e. the maximum over
normalized states `ψ` of `‖(R_n̂(α) − R_n̂(α+β))ψ‖` (eq. 4.61) — between two rotations about a
common unit axis
`n̂` equals `‖1 − exp(iβ/2)‖`. It depends only on the angle difference `β`, never on the base angle
`α`. -/
theorem rotAxis_opNorm_sub (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (α β : ℝ) :
    ‖rotAxisCLM n α - rotAxisCLM n (α + β)‖
      = ‖(1 : ℂ) - Complex.exp ((β / 2 : ℝ) * Complex.I)‖ := sorry

/-- **Nielsen & Chuang, Exercise 4.40, eq. (4.76)** — "use eq. (4.77) to justify (4.76)". Suppose
the iterate angles `{kθ mod 4π}` approximate the target `α` arbitrarily well: `hdense` says that
for every `δ > 0` some `k` and integer `m` have `|kθ − α − 4π·m| < δ`. (A genuine hypothesis —
it holds exactly when `θ` is an irrational multiple of `2π`, i.e. `θ/(4π)` is irrational, by the
pigeonhole/equidistribution argument of §4.5.3; it fails for `θ` a rational multiple of `2π`.)
Then for every `ε > 0` some iterate `R_n̂(θ)^k` approximates the rotation `R_n̂(α)` to
operator-norm distance `< ε`. The bridge is the `4π`-periodic bound. -/
theorem exists_pow_opNorm_sub_lt (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (α θ : ℝ)
    (hdense : ∀ δ : ℝ, 0 < δ → ∃ (k : ℕ) (m : ℤ), |(k : ℝ) * θ - α - 4 * Real.pi * m| < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ‖rotAxisCLM n α - rotAxisCLM n θ ^ k‖ < ε := sorry

end AxQM.Concrete
