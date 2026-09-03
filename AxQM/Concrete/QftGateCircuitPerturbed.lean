/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete: the perturbed Figure 5.1 QFT gate circuit (each controlled-`Rₖ` shifted by `+Δ`)

Toward the faithful `Ω(n²/p(n))` lower bound of Nielsen & Chuang, Exercise 5.6 — the approximate
quantum Fourier transform — this file supplies the **imperfect transform `V`** the exercise
compares against the ideal QFT: the Figure 5.1 circuit in which *every* controlled-`Rₖ` phase
rotation is implemented not exactly but with its phase shifted by a common error `Δ`.

## Main declarations
* `qftRkPerturbed k Δ` — the shifted phase gate `Rₖ' = diag(1, e^{2πi/2ᵏ + iΔ})`, and
  `qftRkPerturbed_mem_unitaryGroup` — it is unitary (its lone off-`1` entry is again a unit-modulus
  phase).
* `qftControlledGatePerturbed`, `qftBlockControlledGatesPerturbed`, `qftBlockPerturbed`,
  `qftGateSequencePerturbed`, `qftGateCircuitPerturbed` — the perturbed conditional rotation, block
  cascade, block, full gate list, and circuit matrix.
* `qftGateCircuitPerturbed_mem_unitaryGroup` — the perturbed circuit is still **unitary** (a genuine
  quantum transform `V`).
-/

namespace AxQM.Concrete

open Matrix

/-- **The `+Δ`-perturbed `Rₖ` phase gate** `Rₖ' = diag(1, e^{2πi/2ᵏ + iΔ})`: the ideal
`Rₖ = diag(1, e^{2πi/2ᵏ})` (N&C eq. 5.11) with its rotation phase shifted by the precision error
`Δ`. This is the imperfect conditional rotation of Exercise 5.6's approximate QFT. -/
noncomputable def qftRkPerturbed (k : ℕ) (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I)]

/-- **`Rₖ'` is unitary.** -/
theorem qftRkPerturbed_mem_unitaryGroup (k : ℕ) (Δ : ℝ) :
    qftRkPerturbed k Δ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hz : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 2 ^ k + ↑Δ * Complex.I)
      = -(2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I) := by
    simp only [map_add, map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal, map_pow]
    ring
  have hφ : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I))
      * Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add, hz, neg_add_cancel, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qftRkPerturbed, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hφ]

/-- **The perturbed controlled-`Rₖ'` gate from control wire `c` onto target wire `t`**. -/
noncomputable def qftControlledGatePerturbed (n : ℕ) (Δ : ℝ) (t c : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  mcCtrlSingleQubit finFunctionFinEquiv {c} t (qftRkPerturbed ((c : ℕ) - (t : ℕ) + 1) Δ)

/-- **The perturbed cascade of target `t`'s block**: the perturbed controlled gates from each of
`t`'s control wires. -/
noncomputable def qftBlockControlledGatesPerturbed (n : ℕ) (Δ : ℝ) (t : Fin n) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (qftTargetControls n t).map (qftControlledGatePerturbed n Δ t)

/-- **Target `t`'s perturbed Figure-5.1 block**: the exact Hadamard on wire `t`, followed by its
perturbed controlled-`Rₖ'` cascade. -/
noncomputable def qftBlockPerturbed (n : ℕ) (Δ : ℝ) (t : Fin n) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  qftHadamardGate n t :: qftBlockControlledGatesPerturbed n Δ t

/-- **The perturbed Figure 5.1 gate list**. -/
noncomputable def qftGateSequencePerturbed (n : ℕ) (Δ : ℝ) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  permGate finFunctionFinEquiv (qftBitReversal n)
    :: (List.finRange n).flatMap (qftBlockPerturbed n Δ)

/-- **The perturbed Figure 5.1 QFT circuit** as a `2ⁿ × 2ⁿ` matrix (the imperfect transform `V` of
Exercise 5.6): the reverse product of `qftGateSequencePerturbed`, so the first-listed gate acts
first: the ideal circuit with every controlled-`Rₖ` performed to precision `Δ`. -/
noncomputable def qftGateCircuitPerturbed (n : ℕ) (Δ : ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (qftGateSequencePerturbed n Δ).reverse.prod

/-- **Every gate of the perturbed Figure 5.1 QFT circuit is unitary.** -/
theorem qftGateSequencePerturbed_forall_mem_unitaryGroup (n : ℕ) (Δ : ℝ) :
    ∀ g ∈ qftGateSequencePerturbed n Δ, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  intro g hg
  rw [qftGateSequencePerturbed, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact permGate_mem_unitaryGroup _ _
  · rw [List.mem_flatMap] at hg
    obtain ⟨t, _, hgt⟩ := hg
    rw [qftBlockPerturbed, List.mem_cons] at hgt
    rcases hgt with rfl | hmap
    · exact singleQubitOnWire_mem_unitaryGroup _ _ hadamardC_mem_unitaryGroup
    · rw [qftBlockControlledGatesPerturbed, List.mem_map] at hmap
      obtain ⟨c, _, rfl⟩ := hmap
      exact mcCtrlSingleQubit_mem_unitaryGroup _ _ _ (qftRkPerturbed_mem_unitaryGroup _ _)

/-- **The perturbed QFT circuit is unitary** — a genuine quantum transform `V` (Nielsen & Chuang, p.
219). -/
theorem qftGateCircuitPerturbed_mem_unitaryGroup (n : ℕ) (Δ : ℝ) :
    qftGateCircuitPerturbed n Δ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  Submonoid.list_prod_mem _ fun g hg =>
    qftGateSequencePerturbed_forall_mem_unitaryGroup n Δ g (List.mem_reverse.mp hg)

end AxQM.Concrete
