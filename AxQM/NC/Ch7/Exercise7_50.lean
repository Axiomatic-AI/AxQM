/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRGroverOracle
import AxQM.NC.Ch7.Exercise7_41

/-!
# Nielsen & Chuang, Exercise 7.50 (NMR Grover oracles for `x₀ = 0, 1, 2`)

*(N&C p. 339.)*

Find quantum circuits using single-qubit rotations and e^{-iH/2ℏJ} to implement the Grover oracle O
for x0=0,1,2.

* `nmrGroverOracleZero_eq_globalPhaseGate_comp`
* `nmrGroverOracleZero_evolve_eq_groverOracleZero`
* `nmrGroverOracleOne_eq_globalPhaseGate_comp`
* `nmrGroverOracleOne_evolve_eq_groverOracleOne`
* `nmrGroverOracleTwo_eq_globalPhaseGate_comp`
* `nmrGroverOracleTwo_evolve_eq_groverOracleTwo`
-/

noncomputable section

namespace AxQM

/-! ### `x₀ = 0` -/

/-- **Exercise 7.50, `x₀ = 0` — the NMR circuit equals the oracle up to a global phase.** The
`R_x(π)`-pulse / `nmrControlledZSequence` circuit `nmrGroverOracleZero c t` equals the ideal
oracle `groverOracleZero` (`= diag(-1,1,1,1)`, the sign flip of `|00⟩`) up to the global phase
`e^{-i7π/4}`. -/
theorem nmrGroverOracleZero_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrGroverOracleZero c t = (globalPhaseGate (-(7 * Real.pi / 4))).comp groverOracleZero := sorry

/-- **Exercise 7.50, `x₀ = 0` — the channel reading.** `nmrGroverOracleZero c t` induces the *same
state channel* `ρ ↦ U ρ U†` as the ideal `x₀ = 0` oracle `groverOracleZero`, on every state `ρ`. -/
theorem nmrGroverOracleZero_evolve_eq_groverOracleZero (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrGroverOracleZero c t).evolve ρ = groverOracleZero.evolve ρ := sorry

/-! ### `x₀ = 1` -/

/-- **Exercise 7.50, `x₀ = 1` — the NMR circuit equals the oracle up to a global phase.** The
`R_x(π)₁`-conjugated `nmrControlledZSequence` circuit `nmrGroverOracleOne c t` equals the ideal
oracle `groverOracleOne` (`= diag(1,-1,1,1)`, the sign flip of `|01⟩`) up to the global phase
`e^{-i3π/4}`. -/
theorem nmrGroverOracleOne_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrGroverOracleOne c t = (globalPhaseGate (-(3 * Real.pi / 4))).comp groverOracleOne := sorry

/-- **Exercise 7.50, `x₀ = 1` — the channel reading.** `nmrGroverOracleOne c t` induces the same
state channel as the ideal `x₀ = 1` oracle `groverOracleOne`, on every state `ρ`. -/
theorem nmrGroverOracleOne_evolve_eq_groverOracleOne (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrGroverOracleOne c t).evolve ρ = groverOracleOne.evolve ρ := sorry

/-! ### `x₀ = 2` -/

/-- **Exercise 7.50, `x₀ = 2` — the NMR circuit equals the oracle up to a global phase.** The
`R_x(π)₂`-conjugated `nmrControlledZSequence` circuit `nmrGroverOracleTwo c t` equals the ideal
oracle `groverOracleTwo` (`= diag(1,1,-1,1)`, the sign flip of `|10⟩`) up to the global phase
`e^{-i3π/4}`. -/
theorem nmrGroverOracleTwo_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrGroverOracleTwo c t = (globalPhaseGate (-(3 * Real.pi / 4))).comp groverOracleTwo := sorry

/-- **Exercise 7.50, `x₀ = 2` — the channel reading.** `nmrGroverOracleTwo c t` induces the same
state channel as the ideal `x₀ = 2` oracle `groverOracleTwo`, on every state `ρ`. -/
theorem nmrGroverOracleTwo_evolve_eq_groverOracleTwo (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrGroverOracleTwo c t).evolve ρ = groverOracleTwo.evolve ρ := sorry

end AxQM
