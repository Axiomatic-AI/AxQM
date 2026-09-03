/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRControlledZ
import AxQM.Basic.API.HadamardABC
import AxQM.Concrete.NMRPulsePhases

/-!
# AxQM.Basic.API — the NMR Bell-preparation circuit (N&C Ex 7.48)

The **bottom-left circuit of Nielsen & Chuang Figure 7.19** (§7.7.3, p. 338): the NMR pulse
sequence that creates the Bell state `(|00⟩ − |11⟩)/√2` from the computational `|00⟩` input.
-/

open scoped InnerProductSpace TensorProduct

open Complex (I)

noncomputable section

namespace AxQM

/-- **The NMR Bell-preparation circuit** (Nielsen & Chuang Figure 7.19, bottom-left; Exercise 7.48):
`(1 ⊗ R_y(-π/2)) · exp(-i(π/4) Z₁Z₂) · (R_x(π/2) ⊗ R_x(π/2))` — an `R_x(π/2)` on each spin, one
period of the `Z₁Z₂`-coupled free evolution, then an `R_y(-π/2)` on the second spin. Applied to
`|00⟩` it creates the Bell state `(|00⟩ − |11⟩)/√2` up to the global phase `e^{-iπ/4}`. -/
def nmrBellCircuit (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotYGate (-(Real.pi / 2))).onRight qubit).comp
    (((couplingZZHamiltonian c).propagator 1 0 t).comp
      (((rotXGate (Real.pi / 2)).onLeft qubit).comp
        ((rotXGate (Real.pi / 2)).onRight qubit)))

end AxQM
