/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.DualRail

/-!
# Nielsen & Chuang, Exercise 7.7 (phase shift on a dual-rail qubit)

*(N&C p. 291.)*

Show the phase-shift circuit transforms a dual-rail state by diag(e^{iπ},1).

* `phaseShiftCircuit`
* `phaseShiftCircuit_evolvePure_dualRail` — the circuit sends the dual-rail state with
  amplitudes `(c₀, c₁)` to the one with amplitudes `(e^{iπ}c₀, c₁)`, i.e. it acts by the matrix
  `diag(e^{iπ}, 1)` of (7.23) on the logical amplitude vector `|ψ_in⟩`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Exercise 7.7 optical circuit**: a phase shifter `P(π)` on the `|01⟩` mode of a dual-rail
qubit, i.e. `1 ⊗ P(π)` on the second factor of `qubit ⊗ qubit` (`(phaseShiftGate π).onRight qubit`).
The boxed-`π` phase shifter of the exercise's figure. -/
def phaseShiftCircuit : Evolution (qubit ⊗ qubit) := (phaseShiftGate Real.pi).onRight qubit

/-- **Exercise 7.7 (7.23):** the phase-shift circuit transforms the dual-rail state by `diag(e^{iπ},
1)`. Acting on `|ψ_in⟩ = c₀|01⟩ + c₁|10⟩` it produces `e^{iπ}c₀|01⟩ + c₁|10⟩`. This is precisely
the matrix `diag(e^{iπ}, 1)` acting on the logical amplitude vector `(c₀, c₁)`. (The output
amplitudes are again normalised since `‖e^{iπ}‖ = 1`.) -/
theorem phaseShiftCircuit_evolvePure_dualRail (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    phaseShiftCircuit.evolvePure (dualRail c0 c1 h)
      = dualRail (Complex.exp ((Real.pi : ℂ) * Complex.I) * c0) c1
          (by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact h) := sorry

end AxQM
