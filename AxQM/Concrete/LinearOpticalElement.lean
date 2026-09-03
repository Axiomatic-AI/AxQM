/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.ComplexExpUnit

/-!
# Concrete: beamsplitters and phase shifters generate every two-level unitary

Nielsen & Chuang, Problem 7.2 (p. 346), *Computing with linear optics*, considers quantum
computation with a single photon in a **unary** mode encoding: an `n`-qubit computational-basis
state `|k⟩` is a single photon occupying mode `k` of `d = 2ⁿ` optical modes, so an arbitrary
`n`-qubit gate is a `d × d` unitary acting on the mode amplitudes `Fin d → ℂ`. Part 1 asks to show
that any such unitary can be built entirely from two passive linear-optical elements —
**beamsplitters** and **phase shifters** — and no nonlinear media.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **Phase shifter on mode `p`.** The diagonal `d × d` matrix `diag(…, e^{iφ}, …)` with the phase
`e^{iφ}` in position `p` and `1` on every other mode. -/
noncomputable def phaseMode (p : Fin d) (φ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i = p then Complex.exp ((φ : ℂ) * Complex.I) else 1)

/-- **Beamsplitter mixing modes `p` and `q`.** The two-level embedding of the real rotation block
`R_y(θ)` into the coordinate pair `{p, q}`: it applies the `2 × 2` rotation
`!![cos(θ/2), -sin(θ/2); sin(θ/2), cos(θ/2)]` to the amplitudes of modes `p, q` and fixes all other
modes — the passive beamsplitter's action on the two spatial modes it couples. -/
noncomputable def beamSplitter (p q : Fin d) (θ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  twoLevelEmbed p q (rotY θ)

/-- **A phase shifter is unitary.** -/
theorem phaseMode_mem_unitaryGroup (p : Fin d) (φ : ℝ) :
    phaseMode p φ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseMode,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs with h
  · exact star_exp_ofReal_mul_I_mul_self φ
  · simp

/-- **A beamsplitter is unitary** (for distinct modes `p ≠ q`). -/
theorem beamSplitter_mem_unitaryGroup {p q : Fin d} (h : p ≠ q) (θ : ℝ) :
    beamSplitter p q θ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  (isTwoLevelUnitary_twoLevelEmbed h (rotY_mem_unitaryGroup θ)).1

end AxQM.Concrete
