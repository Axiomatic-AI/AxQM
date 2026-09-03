/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.InverseQuantumFourierTransform
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.UniformSuperposition
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# AxQM.Basic.API — the qudit phase-gradient state

The **phase-gradient state** `|φ_θ⟩ = (1/√d) ∑ₖ e^{iθk} |k⟩` of the register `qudit d`: the equal
superposition of all computational-basis states, with the `k`-th amplitude carrying the linear phase
`e^{iθk}`. It is the state a phase-estimation register holds after the controlled-power stage has
loaded a per-value linear phase gradient with slope `θ`, and the object the terminal inverse QFT
then reads out (N&C §5.2, Figure 5.2).

## Main declarations
-/

noncomputable section

namespace AxQM

open scoped Matrix

/-- **The nearest computational bin to a phase-gradient slope.** For real slope `θ` and register
size `d`, `nearestBin θ d : Fin d` is the computational-basis index `round(θ·d/(2π)) mod d` —
the bin whose phase `2π·(nearestBin θ d)/d` best matches `θ`, i.e. the best `⌈log₂ d⌉`-bit
estimate of the frequency `θ/(2π)`. The `round` picks the closest integer (`abs_sub_round`), and
`mod d` folds it into `Fin d` (absorbing the `2π` wrap-around when `θ/(2π)` is near `1`). -/
def nearestBin (θ : ℝ) (d : ℕ) [NeZero d] : Fin d :=
  ⟨(round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ)).toNat, by
    have hdℤpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have h1 : 0 ≤ round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d)
    have h2 : round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ) < d := Int.emod_lt_of_pos _ hdℤpos
    exact (Int.toNat_lt h1).mpr h2⟩

end AxQM
