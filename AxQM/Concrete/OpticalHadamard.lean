/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LinearOpticalElement
import AxQM.Concrete.Hadamard

/-!
# Concrete: the optical Hadamard circuit (Nielsen & Chuang, Exercise 7.9)

Nielsen & Chuang, Exercise 7.9 (*Optical Hadamard gate*, p. 292), asks to show that a particular
linear-optical circuit — a phase shifter followed by a beamsplitter — acts as a **Hadamard gate**
on the dual-rail single-photon qubit, i.e.
`|01⟩ → (|01⟩ + |10⟩)/√2` and `|10⟩ → (|01⟩ − |10⟩)/√2`, up to an overall phase.

## Main declarations
* `opticalHadamardCircuit` — the circuit matrix `beamSplitter 0 1 (π/2) * phaseMode 0 π` (circuit
  order left-to-right = matrix product right-to-left: the photon meets the phase shifter first).
* `opticalHadamardCircuit_eq_smul_hadamardC` — the circuit equals the Hadamard matrix up to the
  overall phase `e^{iπ}`, `opticalHadamardCircuit = e^{iπ} • hadamardC`: the circuit *is* a
  Hadamard gate up to a physically irrelevant global phase.
* `opticalHadamardCircuit_mulVec_zeroOne` / `_oneZero` — the explicit action on the two dual-rail
  basis states, `|01⟩ ↦ -(√2)⁻¹(|01⟩ + |10⟩)` and `|10⟩ ↦ -(√2)⁻¹(|01⟩ − |10⟩)`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The optical Hadamard circuit of Nielsen & Chuang, Exercise 7.9.** A phase shifter `phaseMode 0
π` on the top mode followed by a beamsplitter `beamSplitter 0 1 (π/2)` (N&C's `B(π/4)`); as a matrix
the circuit is the product `beamSplitter 0 1 (π/2) * phaseMode 0 π` (the photon passes the phase
shifter first, so it is the right factor). -/
noncomputable def opticalHadamardCircuit : Matrix (Fin 2) (Fin 2) ℂ :=
  beamSplitter 0 1 (Real.pi / 2) * phaseMode 0 Real.pi

/-- **Nielsen & Chuang, Exercise 7.9: the optical circuit is a Hadamard gate up to global phase.**
`opticalHadamardCircuit = e^{iπ} • hadamardC`, the Hadamard up to the overall phase
`e^{iπ} = -1`. -/
theorem opticalHadamardCircuit_eq_smul_hadamardC :
    opticalHadamardCircuit = Complex.exp ((Real.pi : ℂ) * Complex.I) • hadamardC := sorry

/-- **Action on the logical `|01⟩` state.** The circuit sends `|01⟩ = ![1, 0]` to
`-(√2)⁻¹ (|01⟩ + |10⟩)`, i.e. `(|01⟩ + |10⟩)/√2` up to the overall phase `-1 = e^{iπ}`. -/
theorem opticalHadamardCircuit_mulVec_zeroOne :
    opticalHadamardCircuit *ᵥ ![1, 0] = (-(Real.sqrt 2)⁻¹ : ℂ) • ![1, 1] := sorry

/-- **Action on the logical `|10⟩` state.** The circuit sends `|10⟩ = ![0, 1]` to
`-(√2)⁻¹ (|01⟩ − |10⟩)`, i.e. `(|01⟩ − |10⟩)/√2` up to the overall phase `-1 = e^{iπ}`. -/
theorem opticalHadamardCircuit_mulVec_oneZero :
    opticalHadamardCircuit *ᵥ ![0, 1] = (-(Real.sqrt 2)⁻¹ : ℂ) • ![1, -1] := sorry

end AxQM.Concrete
