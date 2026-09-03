/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRControlledNot

/-!
# Nielsen & Chuang, Exercise 7.47 (NMR controlled-`NOT`)

*(N&C p. 338.)*

NMR controlled-NOT gate: verify the Fig 7.19 circuit is a CNOT up to single-qubit phases; give a
proper CNOT circuit.

* `nmrCnot_globalPhase_correction_eq_cnotGate` — the exact gate identity `globalPhase(π/4) ∘
  R_z(π/2)₁ ∘ R_z(-π/2)₂ ∘ nmrCnotCircuit c t = cnotGate`: the Fig 7.19 circuit is the
  controlled-`NOT` up to two single-qubit `z`-rotations and a global phase.
* `properNmrCnot` — the `R_z`-corrected circuit, from the same building blocks.
* `properNmrCnot_evolve_eq_cnotGate` — that circuit induces the CNOT state channel on every
  input; the residual global phase is physically unobservable.
-/

noncomputable section

namespace AxQM

/-- **Exercise 7.47 — the Fig 7.19 circuit is a controlled-`NOT` up to single-qubit `R_z` phases.**
For one coupling period `c·t = π/4`, prefixing the Fig 7.19 circuit `nmrCnotCircuit c t` (a
`90°` `y`-pulse, the `Z₁Z₂` coupling, a `90°` `x`-pulse) with the two single-qubit `z`-rotations
`R_z(π/2)` on the control and `R_z(-π/2)` on the target, and the global phase `e^{iπ/4}`, gives
*exactly* the controlled-`NOT` gate:

`globalPhase(π/4) ∘ R_z(π/2)₁ ∘ R_z(-π/2)₂ ∘ nmrCnotCircuit c t = cnotGate`.
-/
theorem nmrCnot_globalPhase_correction_eq_cnotGate (c t : ℝ) (h : c * t = Real.pi / 4) :
    (globalPhaseGate (Real.pi / 4)).comp
        (((rotZGate (Real.pi / 2)).onLeft qubit).comp
          (((rotZGate (-(Real.pi / 2))).onRight qubit).comp (nmrCnotCircuit c t)))
      = cnotGate := sorry

/-- **Exercise 7.47 — another circuit, from the same building blocks, that realises a *proper*
controlled-`NOT`.** The Fig 7.19 circuit followed by the two single-qubit `z`-rotations `R_z(π/2)`
on the control and `R_z(-π/2)` on the target — the *same building blocks* (single-qubit rotations
and one `Z₁Z₂` coupling period), no global phase needed. -/
def properNmrCnot (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotZGate (Real.pi / 2)).onLeft qubit).comp
    (((rotZGate (-(Real.pi / 2))).onRight qubit).comp (nmrCnotCircuit c t))

/-- **Exercise 7.47 — the proper controlled-`NOT` circuit realises the CNOT channel.** For one
coupling period `c·t = π/4`, the `R_z`-corrected Fig 7.19 circuit `properNmrCnot c t` induces the
*same state channel* `ρ ↦ U ρ U†` as the genuine controlled-`NOT` gate, on **every** state `ρ`:
the residual global phase `e^{iπ/4}` is physically unobservable, so these single-qubit rotations
plus one coupling period realise a proper CNOT. -/
theorem properNmrCnot_evolve_eq_cnotGate (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (properNmrCnot c t).evolve ρ = cnotGate.evolve ρ := sorry

end AxQM
