/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.StabilizerGeneratorFlip

/-!
# Concrete: the stabilizer-formalism verification of quantum teleportation (N&C Ex 10.42)

This file verifies the teleportation circuit of Nielsen & Chuang **Figure 1.13** (p. 27) **in the
stabilizer (Heisenberg) picture** — the content of **Exercise 10.42** (§10.5.4, p. 464).
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

/-- The **byproduct correction** `Z₂^{m₀} X₂^{m₁}` on Bob's wire `2`, as a matrix on the three-qubit
register.  This is the Pauli operation Alice's measurement outcomes `(m₀, m₁)` instruct Bob to apply
(N&C p. 27). -/
def teleportByproduct (m₀ m₁ : Fin 2) : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  pauliString ![0, 0, 3] ^ (m₀ : ℕ) * pauliString ![0, 0, 1] ^ (m₁ : ℕ)

/-- **Teleportation verified — `Z`-basis input.**  For a `Z`-basis stabilizer input `|a⟩` (`a : Fin
2`, `Z₀|a⟩ = (-1)^a|a⟩`), the post-measurement state `w` of Fig 1.13 is a `±1` eigenstate of the
measured `Z₁` with outcome `(-1)^{m₁}` (`h1`) and is stabilised by `(-1)^a Z₁Z₂` (`hstab`).
Then after Bob's byproduct correction his wire is stabilised by `(-1)^a Z₂`:
`Z₂ · (Z₂^{m₀}X₂^{m₁} w) = (-1)^a · (Z₂^{m₀}X₂^{m₁} w)`, i.e. Bob holds the input
state `|a⟩`. -/
theorem teleportation_Zbasis (m₀ m₁ a : Fin 2) (w : (Fin 3 → Fin 2) → ℂ)
    (h1 : (pauliString ![0, 3, 0]).mulVec w = (-1 : ℂ) ^ (m₁ : ℕ) • w)
    (hstab : (pauliString ![0, 3, 3]).mulVec w = (-1 : ℂ) ^ (a : ℕ) • w) :
    (pauliString ![0, 0, 3]).mulVec ((teleportByproduct m₀ m₁).mulVec w)
      = (-1 : ℂ) ^ (a : ℕ) • (teleportByproduct m₀ m₁).mulVec w := sorry

/-- **Teleportation verified — `X`-basis input.**  For an `X`-basis stabilizer input (`b : Fin 2`,
`X₀`-eigenvalue `(-1)^b`), the post-measurement state `w` is a `±1` eigenstate of the measured
`Z₀` with outcome `(-1)^{m₀}` (`h0`) and is stabilised by `(-1)^b Z₀X₂` (`hstab`).
Then after Bob's byproduct correction his wire is stabilised by `(-1)^b X₂`:
`X₂ · (Z₂^{m₀}X₂^{m₁} w) = (-1)^b · (Z₂^{m₀}X₂^{m₁} w)`, i.e. Bob holds the input
`X`-eigenstate. -/
theorem teleportation_Xbasis (m₀ m₁ b : Fin 2) (w : (Fin 3 → Fin 2) → ℂ)
    (h0 : (pauliString ![3, 0, 0]).mulVec w = (-1 : ℂ) ^ (m₀ : ℕ) • w)
    (hstab : (pauliString ![3, 0, 1]).mulVec w = (-1 : ℂ) ^ (b : ℕ) • w) :
    (pauliString ![0, 0, 1]).mulVec ((teleportByproduct m₀ m₁).mulVec w)
      = (-1 : ℂ) ^ (b : ℕ) • (teleportByproduct m₀ m₁).mulVec w := sorry

end AxQM.Concrete
