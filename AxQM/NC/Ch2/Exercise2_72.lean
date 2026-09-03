/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.MaximallyMixed
import AxQM.NC.Ch2.Exercise2_71

/-!
# Nielsen & Chuang, Exercise 2.72 — the Bloch sphere for mixed states

*(N&C p. 105.)*

Bloch sphere for mixed states: rho=(I+r.sigma)/2, ||r||<=1, pure iff ||r||=1.

* `exists_blochState` — part (1): every qubit state `ρ : State qubit` is `blochState r h` for some
  Bloch vector `r` with `‖r‖² = r₀² + r₁² + r₂² ≤ 1`.
* `blochState_zero_eq_maximallyMixed`
* `blochState_isPure_iff_norm_one` — part (3): a qubit state is pure iff its Bloch vector is a unit
  vector, `(blochState r h).IsPure ↔ ‖r⃗‖² = r₀² + r₁² + r₂² = 1` (i.e. `‖r⃗‖ = 1`, since `‖r⃗‖ ≥
  0`).
* `blochPureState_toState_eq_blochState` — part (4): for pure states the Bloch vector coincides with
  the §1.2 parametrization.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.72(1): every qubit density operator is a Bloch state.** For any
qubit state `ρ`, there is a real three-vector `r` with `‖r‖² = r₀² + r₁² + r₂² ≤ 1` such that `ρ
= blochState r h`, i.e. `ρ = ½(I + r⃗·σ⃗)` (eq. 2.175). The vector `r` is the state's Bloch
vector, lying in the closed unit ball `‖r⃗‖ ≤ 1`.
-/
theorem State.exists_blochState (ρ : State qubit) :
    ∃ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1), ρ = blochState r h := sorry

/-- **Nielsen & Chuang, Exercise 2.72(2): the Bloch representation of `ρ = I/2` is `r⃗ = 0`.** The
state with Bloch vector `r⃗ = 0` is the maximally mixed state `I/2` — `blochState 0 =
maximallyMixedState qubit`. -/
theorem blochState_zero_eq_maximallyMixed :
    blochState (0 : Fin 3 → ℝ) (by simp) = maximallyMixedState qubit := sorry

/-- **Nielsen & Chuang, Exercise 2.72(3): a qubit state is pure iff `‖r⃗‖ = 1`.** The Bloch state `ρ
= ½(I + r⃗·σ⃗)` is pure exactly when its Bloch vector is a unit vector, `(blochState r h).IsPure
↔ r₀² + r₁² + r₂² = 1` (i.e. `‖r⃗‖ = 1`, since `‖r⃗‖ ≥ 0`).
-/
theorem blochState_isPure_iff_norm_one (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (blochState r h).IsPure ↔ r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 := sorry

/-- **Nielsen & Chuang, Exercise 2.72(4): for pure states the Bloch vector coincides with the §1.2
parametrization.** The §1.2 single-qubit pure state `|ψ(θ,φ)⟩ = cos(θ/2)|0⟩ + e^{iφ}
sin(θ/2)|1⟩` (eq. 1.4, `blochPureState θ φ`) is the Bloch state `blochState (blochSphereVector θ
φ)` whose Bloch vector is the §1.2 Cartesian point `r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)`: its
density operator `|ψ⟩⟨ψ|` equals `½(I + r⃗·σ⃗)` (eq. 2.175) for exactly the §1.2 vector.

So the Bloch vector attached to a pure state by the mixed-state representation of part (1) — the
`r⃗` read off `ρ = ½(I + r⃗·σ⃗)` — coincides with the §1.2 Bloch-sphere point of the state. The
side condition `‖r⃗‖ ≤ 1` in fact holds with equality, matching part (3): pure states lie on the
surface.
-/
theorem blochPureState_toState_eq_blochState (θ φ : ℝ) :
    (blochPureState θ φ).toState
      = blochState (Concrete.blochSphereVector θ φ) (Concrete.blochSphereVector_normSq θ φ).le :=
        sorry

end AxQM
