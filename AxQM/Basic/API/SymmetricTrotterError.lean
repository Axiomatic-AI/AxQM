/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SymmetricTrotter
import AxQM.Basic.API.ApproxError

/-!
# AxQM.Basic.API — error of the symmetric (Strang) Trotter step (N&C Exercise 4.50)

Both parts of Nielsen & Chuang, Exercise 4.50, expressed in
Box 4.1's *error* notation `E(U,V) = ‖U.op − V.op‖` (`Evolution.gateError`, N&C eq. 4.61). Writing a
Hamiltonian as an ordered sum `H = Σₖ Hₖ` of Hamiltonians (each an `Observable`), the symmetric
(Strang) Trotter step is the palindromic product of the component propagators (N&C eq. 4.106).

## Main declarations
* `Observable.symmTrotterStep_gateError_le` — **Exercise 4.50(a)** in the `E(U,V)` notation: the
  third-order per-step bound `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` for `Δt ∈ [0, 1]`.
* `Observable.symmTrotterStep_gateError_pow_le` — **Exercise 4.50(b)** (N&C eq. 4.107): the
  `m`-step bound `E(U_Δtᵐ, e^{-2miHΔt}) ≤ m·α·Δt³`, with `α` the per-step constant of part (a).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 4.50(a)**, stated in Box 4.1's error notation
`E(U,V) = ‖U.op − V.op‖` (`Evolution.gateError`). For a Hamiltonian decomposition `H = Σₖ Hₖ`
(`H.op = (Hs.map Observable.op).sum`), the symmetric (Strang) Trotter step
`U_Δt = Observable.symmTrotterStep Hs Δt` (the palindromic product of the component propagators, N&C
eq. 4.106) approximates the full half-step-doubled propagator `e^{-2iHΔt} = H.propagator 1 0 (2Δt)`
to *third* order: there is a constant `C ≥ 0` with `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` for every
`Δt ∈ [0, 1]`. -/
theorem Observable.symmTrotterStep_gateError_le
    (H : Observable S) (Hs : List (Observable S)) (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δt : ℝ, 0 ≤ Δt → Δt ≤ 1 →
      (Observable.symmTrotterStep Hs Δt).gateError (H.propagator 1 0 (2 * Δt)) ≤ C * Δt ^ 3 := sorry

/-- **Nielsen & Chuang, Exercise 4.50(b)** (eq. 4.107). Running the symmetric Trotter step `m` times
approximates the exact long-time evolution `e^{-2miHΔt}` with an error that grows at most linearly
in `m`: for a Hamiltonian decomposition `H = Σₖ Hₖ` there is a constant `α ≥ 0` (the third-order
per-step constant of part (a)) with `E(U_Δtᵐ, e^{-2miHΔt}) ≤ m·α·Δt³` for every `m : ℕ` and
`Δt ∈ [0, 1]`, where `U_Δt = Observable.symmTrotterStep Hs Δt` and
`e^{-2miHΔt} = H.propagator 1 0 (2mΔt)`. (N&C's "positive integer `m`" is here stated for all
`m : ℕ`; the `m = 0` case is `0 ≤ 0` and the content is in `m ≥ 1`.)
-/
theorem Observable.symmTrotterStep_gateError_pow_le
    (H : Observable S) (Hs : List (Observable S)) (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (m : ℕ) (Δt : ℝ), 0 ≤ Δt → Δt ≤ 1 →
      (Observable.symmTrotterStep Hs Δt ^ m).gateError (H.propagator 1 0 (2 * (m : ℝ) * Δt))
        ≤ (m : ℝ) * α * Δt ^ 3 := sorry

end AxQM
