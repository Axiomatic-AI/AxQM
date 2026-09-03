/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli

/-!
# Concrete: the multiply-controlled single-qubit gate `Cᵏ(Ũ)` (N&C §4.3 / Barenco)

The gate that applies a `2 × 2` block `Ũ` to a target wire when every wire in a control set `S`
is set to `1`, and acts as the identity otherwise.
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **The multiply-controlled single-qubit gate** `Cᵏ(Ũ)` (`k = |S|`). Relative to an encoding
`enc : (Fin m → Fin 2) ≃ Fin d`, a control set `S`, a target wire `j`, and a `2 × 2` matrix `Ũ`, on
the basis state `|enc x⟩` it applies `Ũ` to bit `j` of `x` when every control wire in `S` is set to
`1`, and acts as the identity otherwise. It is the fibrewise gate whose block is `Ũ` on the
controlled fibres and `1` elsewhere. -/
def mcCtrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m)
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  wireGate enc j (fun y => if ∀ k ∈ S, y k = 1 then Ũ else 1)

/-- **The block algebra is multiplicative on a fixed control set**:
`mcCtrlSingleQubit enc S j P * mcCtrlSingleQubit enc S j Q = mcCtrlSingleQubit enc S j (P * Q)`. -/
theorem mcCtrlSingleQubit_mul (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m)
    (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc S j P * mcCtrlSingleQubit enc S j Q
      = mcCtrlSingleQubit enc S j (P * Q) := by
  rw [mcCtrlSingleQubit, mcCtrlSingleQubit, mcCtrlSingleQubit, wireGate_mul]
  congr 1
  funext y
  by_cases h : ∀ k ∈ S, y k = 1
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, mul_one]

/-- **The multiply-controlled gate of the identity block is the identity.** -/
theorem mcCtrlSingleQubit_one (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m) :
    mcCtrlSingleQubit enc S j (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [mcCtrlSingleQubit]
  simp only [ite_self, wireGate_one]

/-- **The multiply-controlled gate commutes with the conjugate transpose**. -/
theorem mcCtrlSingleQubit_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    (j : Fin m) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    (mcCtrlSingleQubit enc S j Ũ)ᴴ = mcCtrlSingleQubit enc S j Ũᴴ := by
  rw [mcCtrlSingleQubit, mcCtrlSingleQubit, wireGate_conjTranspose]
  congr 1
  funext y
  simp only [apply_ite Matrix.conjTranspose, Matrix.conjTranspose_one]

/-- **A multiply-controlled single-qubit gate with unitary block is unitary.** -/
theorem mcCtrlSingleQubit_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    (j : Fin m) {Ũ : Matrix (Fin 2) (Fin 2) ℂ} (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    mcCtrlSingleQubit enc S j Ũ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hŨ ⊢
  rw [Matrix.star_eq_conjTranspose] at hŨ ⊢
  rw [mcCtrlSingleQubit_conjTranspose, mcCtrlSingleQubit_mul, hŨ, mcCtrlSingleQubit_one]

end AxQM.Concrete
