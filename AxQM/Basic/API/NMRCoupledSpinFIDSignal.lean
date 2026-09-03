/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRCoupledSpinPulsedState

/-!
# AxQM.Basic.API — the coupled two-spin NMR free-induction-decay signal (N&C Ex 7.37)

The **free-induction-decay (FID) signal** `V(t)` of the two-spin, `J`-coupled NMR system of
Nielsen & Chuang Exercise 7.37 (the `H = J Z₁Z₂` half), and its closed-form value. N&C eq. 7.143
defines the signal as `V(t) = V₀ tr[e^{-iHt} ρ e^{iHt} (i Xₖ + Yₖ)]`, the ensemble average of the
(non-Hermitian) transverse magnetization readout `i Xₖ + Yₖ` against the Heisenberg-evolved thermal
state. Here the coupled pair has `k = 1`, `H = J Z₁Z₂`, and `ρ` the `π/2`-pulsed thermal state
`e^{iπY₁/4} ¼(1 − βℏω₀(Z₁+Z₂)) e^{-iπY₁/4}` of the exercise.
-/

open scoped ComplexOrder

noncomputable section

namespace AxQM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **free-induction-decay signal** `V(t) = V₀ tr[e^{-iHt} ρ e^{iHt} (i X₁ + Y₁)]` of the
coupled two-spin NMR system (Nielsen & Chuang eq. 7.143, `k = 1`), for the `J`-coupling Hamiltonian
`H = J Z₁Z₂` and the `π/2`-pulsed thermal initial state `ρ = nmrCoupledPairPulsedState`. The
readout is `nmrTransverseReadout = i X₁ + Y₁`. -/
def nmrCoupledPairFID (V₀ J β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) (t : ℝ) : ℂ :=
  (V₀ : ℂ) • LinearMap.trace ℂ (qubit.compose qubit).space
    ↑((((couplingZZHamiltonian J).propagator 1 0 t).evolve
        (nmrCoupledPairPulsedState β ℏ ω h)).op * nmrTransverseReadout)

/-- **The FID signal of the coupled NMR pair (Nielsen & Chuang Exercise 7.37, `H = J Z₁Z₂`):** `V(t)
= i · V₀ · βℏω₀ · cos(2Jt)`. The free-induction decay of the `π/2`-pulsed thermal state is a
single spectral doublet at `±2J`, with amplitude the transverse magnetization `βℏω₀`. -/
theorem nmrCoupledPairFID_eq (V₀ J β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) (t : ℝ) :
    nmrCoupledPairFID V₀ J β ℏ ω h t
      = Complex.I * (V₀ : ℂ) * ((β * ℏ * ω : ℝ) : ℂ) * (Real.cos (2 * J * t) : ℂ) := sorry

end AxQM
