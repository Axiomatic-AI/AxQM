/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import AxQM.Concrete.PhaseDampingChannel
import AxQM.Concrete.Pauli

/-!
# Concrete: unitality of the single-qubit noise channels (N&C Exercise 8.29)

It records the content of
**Nielsen & Chuang, Exercise 8.29 (Unitality)**.

## Contents

* `depolChannel p ρ` — the **qubit depolarizing channel** in operator-sum form
  `E(ρ) = (1 - 3p/4) ρ + (p/4)(X ρ X + Y ρ Y + Z ρ Z)` (N&C eq. 8.102), on `2 × 2` matrices, and
  `depolChannel_apply_one` — **unital**: `E(I) = I`, since `X X† + Y Y† + Z Z† = 3 I` and
  `(1 - 3p/4) + 3·(p/4) = 1`.
* `phaseDampChannel_apply_one` — the **phase-damping channel is unital**: `E_PD(I) = I`
  (`0 ≤ λ ≤ 1`), via `E₀ E₀† + E₁ E₁† = (P₀ + (1-λ) P₁) + λ P₁ = P₀ + P₁ = I`.
* `ampDampChannel_not_unital` — **amplitude damping is not unital**: `E_AD(I) ≠ I` for `0 < γ`,
  because `E_AD(I) |0⟩ = (1+γ) |0⟩ ≠ |0⟩` — the extra `γ Z` term biases the excited-state
  population toward the ground state (a channel with a preferred fixed point, the `|0⟩` "north
  pole", not the maximally mixed state).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

open Matrix

/-- **The single-qubit depolarizing channel** in operator-sum form `E(ρ) = (1 - 3p/4) ρ + (p/4)(X ρ
X + Y ρ Y + Z ρ Z)` (Nielsen & Chuang eq. 8.102), on `2 × 2` complex matrices. -/
noncomputable def depolChannel (p : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 - 3 * p / 4 : ℝ) : ℂ) • ρ
    + ((p / 4 : ℝ) : ℂ) • (pauliX * ρ * pauliX + pauliY * ρ * pauliY + pauliZ * ρ * pauliZ)

/-- **The depolarizing channel is unital** (Exercise 8.29): `E(I) = I`. Since the Pauli matrices are
involutions (`X I X = X² = I`, likewise `Y`, `Z`), the operator-sum evaluated at the identity is
`(1 - 3p/4) I + (p/4)(I + I + I) = (1 - 3p/4 + 3p/4) I = I`. -/
theorem depolChannel_apply_one (p : ℝ) : depolChannel p 1 = 1 := sorry

section Qubit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- **The phase-damping channel is unital** (Exercise 8.29): `E_PD(I) = I` for `0 ≤ λ ≤ 1`. -/
theorem phaseDampChannel_apply_one (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    phaseDampChannel b lam LinearMap.id = LinearMap.id := sorry

/-- **Amplitude damping is not unital** (Exercise 8.29): `E_AD(I) ≠ I` for `0 < γ`. Evaluating the
value `E_AD(I) = (1+γ) P₀ + (1-γ) P₁` at the ground state gives `E_AD(I) |0⟩ = (1+γ) |0⟩`, whereas
`I |0⟩ = |0⟩`; were they equal we would have `γ |0⟩ = 0`, impossible for `γ ≠ 0` and `|0⟩ ≠ 0`. This
is the asymmetry of amplitude damping: `E₁ = √γ |0⟩⟨1|` moves population into `|0⟩` without a
balancing `|0⟩ → |1⟩` process, so the identity is not preserved. -/
theorem ampDampChannel_not_unital (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ampDampChannel b γ LinearMap.id ≠ LinearMap.id := sorry

end Qubit

end AxQM.Concrete

end
