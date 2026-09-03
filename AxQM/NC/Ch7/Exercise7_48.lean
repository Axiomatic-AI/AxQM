/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRBellPrep

/-!
# Nielsen & Chuang, Exercise 7.48 (NMR Bell-state preparation)

*(N&C p. 338.)*

Verify the bottom-left Fig 7.19 circuit creates the Bell state (|00⟩−|11⟩)/√2.

* `nmrBellCircuit_evolvePure_toState`
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Exercise 7.48: the bottom-left Figure 7.19 NMR circuit creates the Bell state `|β₁₀⟩`.**
Applied to the computational input `|00⟩`, the circuit `nmrBellCircuit c t` (an `R_x(π/2)` on each
spin, one `Z₁Z₂`-coupling period with `c·t = π/4`, then `R_y(-π/2)` on the second spin) prepares a
state whose density operator equals that of the Bell state `|β₁₀⟩ = (|00⟩ − |11⟩)/√2`:
`((nmrBellCircuit c t).evolvePure |00⟩).toState = (bellState 1 0).toState`.

The equality is one of density operators, to which a global phase of unit modulus is invisible: as
physical states the output **is** `|β₁₀⟩` — verifying the exercise's claim. -/
theorem nmrBellCircuit_evolvePure_toState (c t : ℝ) (h : c * t = Real.pi / 4) :
    ((nmrBellCircuit c t).evolvePure ((qubitBasis 0).tmul (qubitBasis 0))).toState
      = (bellState 1 0).toState := sorry

end AxQM
