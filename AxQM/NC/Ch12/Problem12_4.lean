/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Mixture

/-!
# N&C Problem 12.4 — linearity forbids cloning

*(N&C p. 603.)*

Linearity forbids cloning: mixtures of rho1,rho2 not copied by linear procedure.

* `linearity_forbids_cloning`
-/

noncomputable section

namespace AxQM

variable {S B : QSystem}

/-- **Linearity forbids cloning** (Nielsen & Chuang Problem 12.4). Let `E : State (S ⊗ B) → State (S
⊗ S)` be a copying procedure that is **linear on states** — it preserves every binary mixture
(`hlinear`) — and let `σ : State B` be the fixed standard target state. Suppose `E` correctly
copies two *distinct* states `ρ₁ ≠ ρ₂` from the target, `E (ρ₁ ⊗ σ) = ρ₁ ⊗ ρ₁` and `E (ρ₂ ⊗ σ) =
ρ₂ ⊗ ρ₂`. Then for **any** nontrivial mixture `ρ = p ρ₁ + (1 − p) ρ₂` (`0 < p < 1`), the
procedure does **not** copy `ρ`: ``` E (ρ ⊗ σ) ≠ ρ ⊗ ρ. ```
-/
theorem linearity_forbids_cloning (E : State (S ⊗ B) → State (S ⊗ S))
    (hlinear : ∀ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (τ₁ τ₂ : State (S ⊗ B)),
      E (State.mixPair hq0 hq1 τ₁ τ₂) = State.mixPair hq0 hq1 (E τ₁) (E τ₂))
    (σ : State B) {ρ₁ ρ₂ : State S} (hne : ρ₁ ≠ ρ₂)
    (hclone₁ : E (ρ₁.tmul σ) = ρ₁.tmul ρ₁) (hclone₂ : E (ρ₂.tmul σ) = ρ₂.tmul ρ₂)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    E ((State.mixPair hp0.le hp1.le ρ₁ ρ₂).tmul σ)
      ≠ (State.mixPair hp0.le hp1.le ρ₁ ρ₂).tmul (State.mixPair hp0.le hp1.le ρ₁ ρ₂) := sorry

end AxQM
