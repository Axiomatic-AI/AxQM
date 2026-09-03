/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.RotationDecompositionXY
import AxQM.ToMathlib.NumberTheory.CosThreeFifthsIrrational
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.Matrix

/-!
# Concrete: the (uncontrolled) single-qubit gate on a wire (N&C §4.3/§4.5)

(Nielsen & Chuang §4.3, §4.5.2, p. 182–193 — the `n`-qubit lift.)
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The single-qubit gate on wire `j`.** Relative to an encoding `enc : (Fin m → Fin 2) ≃ Fin d`,
a wire `j`, and a `2 × 2` matrix `g`, it applies `g` to bit `j` of `x` on the basis state `|enc x⟩`
(regardless of the other bits), fixing the other bits: `g` acts on every fibre of the `j`-th
bit. -/
def singleQubitOnWire (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i i' =>
    if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then g (enc.symm i j) (enc.symm i' j) else 0

/-- Unfolding lemma for `singleQubitOnWire` entries. -/
theorem singleQubitOnWire_apply (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (i i' : Fin d) :
    singleQubitOnWire enc j g i i' =
      if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then g (enc.symm i j) (enc.symm i' j)
      else 0 := rfl

/-- **`singleQubitOnWire` is the fibrewise gate `wireGate` with a constant block.** -/
theorem singleQubitOnWire_eq_wireGate (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j g = wireGate enc j (fun _ => g) := by
  ext i i'
  simp only [singleQubitOnWire, wireGate, Matrix.of_apply]

/-- The single-qubit wire gate of the `2 × 2` identity is the `d × d` identity. -/
theorem singleQubitOnWire_one (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) :
    singleQubitOnWire enc j (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [singleQubitOnWire_eq_wireGate, wireGate_one]

/-- **`singleQubitOnWire enc j` is multiplicative on the block**: it respects matrix products. -/
theorem singleQubitOnWire_mul (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (a b : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j a * singleQubitOnWire enc j b
      = singleQubitOnWire enc j (a * b) := by
  simp only [singleQubitOnWire_eq_wireGate, wireGate_mul]

/-- **`singleQubitOnWire enc j` commutes with the conjugate transpose**:
`(singleQubitOnWire enc j g)ᴴ = singleQubitOnWire enc j gᴴ`. -/
theorem singleQubitOnWire_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (singleQubitOnWire enc j g)ᴴ = singleQubitOnWire enc j gᴴ := by
  ext i i'
  rw [Matrix.conjTranspose_apply, singleQubitOnWire_apply, singleQubitOnWire_apply,
    Matrix.conjTranspose_apply]
  by_cases hoff : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
  · rw [if_pos hoff, if_pos (fun k hk => (hoff k hk).symm)]
  · rw [if_neg hoff, if_neg (fun h => hoff (fun k hk => (h k hk).symm)), star_zero]

/-- **A single-qubit wire gate with unitary block is unitary.** -/
theorem singleQubitOnWire_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    singleQubitOnWire enc j g ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hg ⊢
  rw [Matrix.star_eq_conjTranspose] at hg ⊢
  rw [singleQubitOnWire_conjTranspose, singleQubitOnWire_mul, hg, singleQubitOnWire_one]

end AxQM.Concrete
