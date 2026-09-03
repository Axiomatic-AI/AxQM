/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Nielsen & Chuang, Exercise 9.17 (The angle between states is a bounded distance)

*(N&C p. 413.)*

Show 0<=A(rho,sigma)<=pi/2 with equality in first iff rho=sigma (angle metric).

* `angle` — the angle metric `A(ρ, σ) = arccos F(ρ, σ)` (N&C `(9.82)`);
* `angle_nonneg` — `0 ≤ A(ρ, σ)`;
* `angle_le_pi_div_two` — `A(ρ, σ) ≤ π/2`;
* `angle_eq_zero_iff` — `A(ρ, σ) = 0 ↔ ρ = σ` (equality in the first inequality iff the states
  coincide) — the heart of Exercise 9.17.
-/

namespace AxQM

variable {S : QSystem}

/-- **The angle between two states** `A(ρ, σ) ≡ arccos F(ρ, σ)` (Nielsen & Chuang `(9.82)`). -/
noncomputable def State.angle (ρ σ : State S) : ℝ := Real.arccos (ρ.fidelity σ)

/-- **The angle is non-negative**, `0 ≤ A(ρ, σ)` — the lower bound of Exercise 9.17. -/
theorem State.angle_nonneg (ρ σ : State S) : 0 ≤ ρ.angle σ := sorry

/-- **The angle is at most `π/2`**, `A(ρ, σ) ≤ π/2` — the upper bound of Exercise 9.17. -/
theorem State.angle_le_pi_div_two (ρ σ : State S) : ρ.angle σ ≤ Real.pi / 2 := sorry

/-- **The angle vanishes exactly when the states coincide**, `A(ρ, σ) = 0 ↔ ρ = σ` — the
"equality in the first inequality" clause of Exercise 9.17. -/
theorem State.angle_eq_zero_iff (ρ σ : State S) : ρ.angle σ = 0 ↔ ρ = σ := sorry

end AxQM
