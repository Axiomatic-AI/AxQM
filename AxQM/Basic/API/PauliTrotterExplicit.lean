/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliTrotterStep
import AxQM.Basic.API.PauliTrotter
import AxQM.Basic.API.PauliExpansion
import AxQM.Basic.API.QuditMeasurement
import AxQM.Concrete.PauliString
import Mathlib.Algebra.Order.Chebyshev
import AxQM.Basic.API.ApproxError
import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-!
# The `k`-fold Trotter circuit approximates `U` with an explicit `O(4ⁿ)` constant (Problem 4.3(6))

This file sharpens the constant.

## Main declarations
* `Evolution.exists_pauliString_trotter_approximation_explicit` — the **explicit** form:
  every `U : Evolution (qudit (2ⁿ))` satisfies
  `‖[∏_g exp(-i h_g g /k)]ᵏ - U‖ ≤ trotterProductConst·(2ⁿ·2π)²·k⁻¹` — an `O(4ⁿ)/k` bound with a
  fully explicit constant.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {n : ℕ}

-- `NormedSpace.trotterProductConst` (`= 2e + e²·eᵉ`) is the fork's single source of truth for the
-- numerical constant of the unitarity-aware Trotter bounds; open it (and its nonnegativity)
-- so the statements read cleanly and match the fork bound's constant by name, not a defeq accident.
open NormedSpace (trotterProductConst trotterProductConst_nonneg)

/-- **Nielsen & Chuang, Problem 4.3(6), operator form with an explicit `O(4ⁿ)` constant.** *Every*
unitary `U` on the `n`-qubit register `qudit (2ⁿ)` is approximated to `O(4ⁿ)/k` by the `k`-fold
Pauli–Trotter product, with a **fully explicit** constant: there are real coefficients `h_g`
with `‖(∏_g exp(-i h_g g /k))ᵏ - U‖ ≤ trotterProductConst · (2ⁿ · 2π)² · k⁻¹` for every `k ≥ 1`.

Since `(2ⁿ · 2π)² = 4ⁿ · (2π)²`, the constant `trotterProductConst · (2ⁿ · 2π)²` is manifestly
`O(4ⁿ)` — N&C's `k = O(4ⁿ/ε)` step count.
-/
theorem Evolution.exists_pauliString_trotter_approximation_explicit
    (U : Evolution (qudit (2 ^ n))) :
    ∃ h : (Fin n → Fin 4) → ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖(Finset.univ.toList.map fun g =>
            ((pauliStringHamiltonian g (h g)).propagator 1 0 (k : ℝ)⁻¹).op).prod ^ k - U.op‖
        ≤ trotterProductConst * (2 ^ n * (2 * Real.pi)) ^ 2 * (k : ℝ)⁻¹ := sorry

end AxQM
