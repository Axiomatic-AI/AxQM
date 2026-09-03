/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HighTempThermalState

/-!
# Nielsen & Chuang, Exercise 7.36 (Thermal-equilibrium NMR state)

*(N&C p. 329.)*

Thermal-equilibrium NMR state: show ρ≈1−(ℏω/2k_BT)Z for n=1 and the n=2 diagonal form.

* `nmrThermalState_spinOne_eq` — Exercise 7.36, `n = 1`: the single-spin high-temperature thermal
  state equals the Bloch state with Bloch vector `(0, 0, −βℏω)`, i.e. `½(I − βℏω Z)` — the matrix `1
  − (ℏω/2k_BT) Z` of eq. 7.141 (with the book's `1` denoting the maximally-mixed identity part `½I`,
  since the literal matrix `1 − (ℏω/2k_BT)Z` has trace `2`, not `1`, and only its traceless part `Z`
  carries physical content).
* `nmrThermalState_spinTwo_eq` — Exercise 7.36, `n = 2`: the two-spin high-temperature thermal state
  equals `nmrThermalStateSpinTwo`, the diagonal state with populations `¼·(1 − 5βℏω_B, 1 − 3βℏω_B, 1
  + 3βℏω_B, 1 + 5βℏω_B)` — the matrix `1 − (ℏω_B/4k_BT)·diag(5, 3, −3, −5)` of eq. 7.142 (again the
  book's `1` is the maximally-mixed identity part `¼I`; only the traceless `diag(5, 3, −3, −5)`
  carries physical content).
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.36 (`n = 1`, eq. 7.141).** The single-spin NMR high-temperature
thermal-equilibrium state `2^{−1}(I − βH)` for the Zeeman Hamiltonian `H = ℏω Z` equals the
qubit Bloch state with Bloch vector `(0, 0, −βℏω)`, i.e. `½(I − βℏω Z)` — the density operator
`1 − (ℏω/2k_BT) Z` of eq. 7.141 (`β = 1/(k_B T)`; the book's leading `1` is the maximally-mixed
part `½I`). The hypothesis `(βℏω)² ≤ 1` is the single-spin high-temperature/positivity condition
(the Bloch vector lies in the unit ball).
-/
theorem nmrThermalState_spinOne_eq (β ℏ ω : ℝ) (hr : (β * ℏ * ω) ^ 2 ≤ 1) :
    highTempThermalState β (nmrHamiltonianSpinOne ℏ ω)
        (highTempThermalStateSpinOne_isDensity β ℏ ω hr)
      = blochState ![0, 0, -(β * ℏ * ω)] (nmrThermalStateSpinOne_bloch_ball β ℏ ω hr) := sorry

/-- **Nielsen & Chuang, Exercise 7.36 (`n = 2`, eq. 7.142).** In the resonance case `ω_A = 4ω_B`,
the two-spin NMR high-temperature thermal-equilibrium state `2⁻²(I − βH)` for the Zeeman
Hamiltonian `H = ℏ(ω_A Z₁ + ω_B Z₂)` equals the diagonal state `nmrThermalStateSpinTwo` with
populations `¼·(1 − 5βℏω_B, 1 − 3βℏω_B, 1 + 3βℏω_B, 1 + 5βℏω_B)` — the density operator `1 −
(ℏω_B/4k_BT)·diag(5, 3, −3, −5)` of eq. 7.142 (`β = 1/(k_B T)`; the book's leading `1` is the
maximally-mixed part `¼I`). The hypothesis `(5βℏω_B)² ≤ 1` is the two-spin high-temperature /
positivity condition (the largest Zeeman population stays in `[0,1]`).
-/
theorem nmrThermalState_spinTwo_eq (β ℏ ωB : ℝ) (h : (5 * (β * ℏ * ωB)) ^ 2 ≤ 1) :
    highTempThermalState β (nmrHamiltonianSpinTwo ℏ (4 * ωB) ωB)
        (highTempThermalStateSpinTwo_isDensity β ℏ ωB h)
      = nmrThermalStateSpinTwo β ℏ ωB h := sorry

end AxQM
