/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Beamsplitter

/-!
# Nielsen & Chuang, Exercise 7.10 (Mach–Zehnder interferometer)

*(N&C p. 292.)*

Mach-Zehnder interferometer: show identity circuit and compute rotation as function of phase φ.

* `machZehnderIdentityCircuit`
* `machZehnderIdentityCircuit_eq_id` — part 1: the circuit *is* the identity `Evolution`,
  `B(-θ) ∘ B(θ) = 1`.
* `machZehnder`
* `machZehnder_amp_normalized` — the output amplitudes are again normalised.
* `machZehnder_evolvePure_dualRail` — part 2 (the computed operation): it sends `c₀|01⟩ + c₁|10⟩` to
  the dual-rail state with amplitudes `½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁),  ½((1-e^{iφ})c₀ +
  (e^{iφ}+1)c₁)`, the rotation operation as an explicit function of the phase `φ`.
* `mz_half_cos`
* `mz_half_sin`
* `machZehnder_rotX_amp_normalized` — the `R_x(φ)` output amplitudes are again normalised.
* `machZehnder_evolvePure_dualRail_rotX` — part 2 (the rotation identified): the same output written
  as `e^{iφ/2}·R_x(φ)` applied to `(c₀, c₁)`, i.e. the amplitudes are `e^{iφ/2}(cos(φ/2)·c₀ -
  i·sin(φ/2)·c₁)` and `e^{iφ/2}(-i·sin(φ/2)·c₀ + cos(φ/2)·c₁)`.
-/

open scoped InnerProductSpace TensorProduct

open Complex

noncomputable section

namespace AxQM

/-! ### Part 1 — two inverse beamsplitters perform the identity -/

/-- The **Exercise 7.10.1 identity circuit**: two beamsplitters `B(-θ)` and `B(θ)` in series, i.e.
`beamSplitterDualRail (-θ) ∘ beamSplitterDualRail θ`. In a Mach–Zehnder interferometer the
recombining beamsplitter is the inverse of the splitting one, so their mixing angles are
opposite. -/
def machZehnderIdentityCircuit (θ : ℝ) : Evolution (qubit ⊗ qubit) :=
  (beamSplitterDualRail (-θ)).comp (beamSplitterDualRail θ)

/-- **Exercise 7.10, part 1: the two-beamsplitter circuit performs the identity operation.** `B(-θ)
∘ B(θ) = 1`. -/
theorem machZehnderIdentityCircuit_eq_id (θ : ℝ) :
    machZehnderIdentityCircuit θ = Evolution.id := sorry

/-! ### Part 2 — the phased interferometer as a rotation by the phase `φ` -/

/-- The **Exercise 7.10.2 Mach–Zehnder circuit**: a phase shifter `P(φ)` on the `|01⟩` mode placed
between two balanced `50/50` beamsplitters `B(π/4)` and `B(-π/4)`, i.e.
`B(-π/4) ∘ P(φ) ∘ B(π/4)` as an `Evolution (qubit ⊗ qubit)` (the photon meets `B(π/4)` first, so it
is the rightmost factor). -/
def machZehnder (φ : ℝ) : Evolution (qubit ⊗ qubit) :=
  (beamSplitterDualRail (-(Real.pi / 4))).comp
    (((phaseShiftGate φ).onRight qubit).comp (beamSplitterDualRail (Real.pi / 4)))

/-- **The output amplitudes of the Mach–Zehnder circuit are normalised:** the rotated amplitudes
`(½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁), ½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁))` satisfy `‖·‖² + ‖·‖² = 1`. -/
theorem machZehnder_amp_normalized (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1)‖ ^ 2
      + ‖2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1)‖ ^ 2
        = 1 := by
  have hop : (machZehnder φ).op (dualRailVec c0 c1)
      = dualRailVec
          (2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1))
          (2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1)) :=
      by
    rw [machZehnder, Evolution.comp_op, Evolution.comp_op,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact machZehnderDualRail_op_apply_dualRailVec φ c0 c1
  rw [← norm_dualRailVec_sq, ← hop, (machZehnder φ).norm_op_apply, norm_dualRailVec c0 c1 h,
    one_pow]

/-- **Exercise 7.10, part 2 (the computed operation).** The balanced Mach–Zehnder circuit sends the
dual-rail state `c₀|01⟩ + c₁|10⟩` to the state with amplitudes
`½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁)` and `½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁)` — the rotation operation the
circuit performs, as an explicit function of the phase shift `φ`. -/
theorem machZehnder_evolvePure_dualRail (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    (machZehnder φ).evolvePure (dualRail c0 c1 h)
      = dualRail
          (2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1))
          (2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1))
          (machZehnder_amp_normalized φ c0 c1 h) := sorry

/-- Half-angle identity `½(e^{iφ} + 1) = e^{iφ/2}·cos(φ/2)`. -/
private theorem mz_half_cos (φ : ℝ) :
    (2 : ℂ)⁻¹ * (Complex.exp ((φ : ℂ) * I) + 1)
      = Complex.exp (((φ / 2 : ℝ) : ℂ) * I) * (Real.cos (φ / 2) : ℂ) := by
  have dc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    have hh := Real.cos_two_mul (φ / 2); rw [show 2 * (φ / 2) = φ by ring] at hh; linarith [hh]
  have ds : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have hh := Real.sin_two_mul (φ / 2); rw [show 2 * (φ / 2) = φ by ring] at hh; linarith [hh]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, dc, ds]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]; ring

/-- Half-angle identity `½(1 - e^{iφ}) = e^{iφ/2}·(-i·sin(φ/2))`. -/
private theorem mz_half_sin (φ : ℝ) :
    (2 : ℂ)⁻¹ * (1 - Complex.exp ((φ : ℂ) * I))
      = Complex.exp (((φ / 2 : ℝ) : ℂ) * I) * (-(I * (Real.sin (φ / 2) : ℂ))) := by
  have dc' : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have hh := Real.cos_two_mul (φ / 2); have hp := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at hh; nlinarith [hh, hp]
  have ds : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have hh := Real.sin_two_mul (φ / 2); rw [show 2 * (φ / 2) = φ by ring] at hh; linarith [hh]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, dc', ds]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
  linear_combination ((Real.sin (φ / 2) : ℂ) ^ 2) * Complex.I_sq

/-- **The `R_x(φ)` output amplitudes are normalised.** -/
theorem machZehnder_rotX_amp_normalized (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
          * ((Real.cos (φ / 2) : ℂ) * c0 - I * (Real.sin (φ / 2) : ℂ) * c1)‖ ^ 2
      + ‖Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
          * (-(I * (Real.sin (φ / 2) : ℂ)) * c0 + (Real.cos (φ / 2) : ℂ) * c1)‖ ^ 2
        = 1 := by
  have e0 : Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
        * ((Real.cos (φ / 2) : ℂ) * c0 - I * (Real.sin (φ / 2) : ℂ) * c1)
      = 2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1) := by
    linear_combination -c0 * mz_half_cos φ - c1 * mz_half_sin φ
  have e1 : Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
        * (-(I * (Real.sin (φ / 2) : ℂ)) * c0 + (Real.cos (φ / 2) : ℂ) * c1)
      = 2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1) := by
    linear_combination -c0 * mz_half_sin φ - c1 * mz_half_cos φ
  rw [e0, e1]; exact machZehnder_amp_normalized φ c0 c1 h

/-- **Exercise 7.10, part 2 (the rotation identified).** The balanced Mach–Zehnder circuit acts on
the dual-rail qubit as `e^{iφ/2}·R_x(φ)`: it sends `c₀|01⟩ + c₁|10⟩` to the state with
amplitudes `e^{iφ/2}(cos(φ/2)·c₀ - i·sin(φ/2)·c₁)` and `e^{iφ/2}(-i·sin(φ/2)·c₀ + cos(φ/2)·c₁)`.
These are `e^{iφ/2}` times the action on `(c₀, c₁)` of `R_x(φ) = e^{-iφX/2}`, whose matrix is
`[[cos(φ/2), -i sin(φ/2)]; [-i sin(φ/2), cos(φ/2)]]`. So up to the unobservable global phase
`e^{iφ/2}` the interferometer performs the `x`-axis rotation by the phase `φ` — the rotation N&C
ask to compute. -/
theorem machZehnder_evolvePure_dualRail_rotX (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    (machZehnder φ).evolvePure (dualRail c0 c1 h)
      = dualRail
          (Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
            * ((Real.cos (φ / 2) : ℂ) * c0 - I * (Real.sin (φ / 2) : ℂ) * c1))
          (Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
            * (-(I * (Real.sin (φ / 2) : ℂ)) * c0 + (Real.cos (φ / 2) : ℂ) * c1))
          (machZehnder_rotX_amp_normalized φ c0 c1 h) := sorry

end AxQM
