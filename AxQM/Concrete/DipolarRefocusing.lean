/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DipolarCoupling

/-!
# Concrete: refocusing the dipolar coupling into the `Z₁Z₂` (weak-coupling) form

**Nielsen & Chuang, Exercise 7.40** (*refocusing dipolar interactions*, p. 332): give a sequence of
pulses that turns the two-spin through-space dipolar coupling `H^D_{1,2}(n̂)` (eq. 7.136) into the
much simpler weak-coupling form of (7.138).
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker BigOperators

/-- The `180°` `ẑ`-refocusing pulse on spin 1, `Z⊗I` (conjugation by the physical pulse `−iZ`). -/
noncomputable def refocusZ₁ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- The `180°` `ẑ`-refocusing pulse on spin 2, `I⊗Z`. -/
noncomputable def refocusZ₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliZ

/-- The joint `180°` `ẑ`-pulse on both spins, `Z⊗Z` — the product of the two single-spin pulses. -/
noncomputable def refocusZ₁₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliZ ⊗ₖ pauliZ

/-- The **toggling-frame (zeroth-order average) Hamiltonian** produced by the `ẑ`-refocusing pulse
cycle: the symmetric average of `H` over conjugation by the four pulses `{I⊗I, Z⊗I, I⊗Z, Z⊗Z}`. -/
noncomputable def zRefocusAverage (H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (4⁻¹ : ℂ) • (H + refocusZ₁ * H * refocusZ₁ + refocusZ₂ * H * refocusZ₂
    + refocusZ₁₂ * H * refocusZ₁₂)

/-- The **residual (secular) dipolar coupling constant** `J_eff = γ₁ γ₂ (1 − 3 n_z²) / r³` left
after the `ẑ`-refocusing pulse sequence (the `∝ (1 − 3 cos²θ)` scaling of the dipolar coupling). -/
noncomputable def dipolarEffectiveCoupling (γ₁ γ₂ r : ℝ) (n : Fin 3 → ℝ) : ℝ :=
  γ₁ * γ₂ * (1 - 3 * (n 2) ^ 2) / r ^ 3

/-- **Nielsen & Chuang, Exercise 7.40 (refocusing dipolar interactions).** The `ẑ`-refocusing pulse
sequence turns the through-space dipolar coupling `H^D_{1,2}(n̂)` into the simple weak-coupling form
of (7.138): its toggling-frame average Hamiltonian is `(ℏ J_eff / 4) • Z₁Z₂`, a pure `Z₁Z₂`
interaction with effective constant `J_eff = γ₁ γ₂ (1 − 3 n_z²) / r³`, for every choice of the
physical constants `γ₁, γ₂, ℏ, r` and every internuclear direction `n̂`. -/
theorem zRefocusAverage_dipolarCoupling (γ₁ γ₂ ℏ r : ℝ) (n : Fin 3 → ℝ) :
    zRefocusAverage (dipolarCoupling γ₁ γ₂ ℏ r n)
      = ((ℏ * dipolarEffectiveCoupling γ₁ γ₂ r n / 4 : ℝ) : ℂ) • (pauliZ ⊗ₖ pauliZ) := sorry

end AxQM.Concrete
