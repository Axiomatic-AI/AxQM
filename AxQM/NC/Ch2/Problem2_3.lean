/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CHSH

/-!
# Nielsen & Chuang, Problem 2.3 (Tsirelson's inequality)

*(N&C p. 118.)*

Tsirelson's inequality: (Q⊗S+R⊗S+R⊗T-Q⊗T)^2 = 4I+[Q,R]⊗[S,T]; bound 2sqrt2.

* `pauliObservable_chsh_expectation_le`
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang (2.234): Tsirelson's bound on the CHSH quantity.** For real unit vectors `q⃗,
r⃗, s⃗, t⃗` — giving the two-qubit Pauli observables `Q = q⃗·σ⃗`, `R = r⃗·σ⃗`, `S = s⃗·σ⃗`, `T =
t⃗·σ⃗` — and any pure state `ψ` of the two-qubit system, `⟪Q⊗S⟫_ψ + ⟪R⊗S⟫_ψ + ⟪R⊗T⟫_ψ - ⟪Q⊗T⟫_ψ
≤ 2√2`.

Since the classical (local-hidden-variable) CHSH bound is `2` and `2√2 > 2`, this shows the
quantum violation is bounded — the value `2√2` is the maximum possible in quantum mechanics.
-/
theorem pauliObservable_chsh_expectation_le (ψ : PureState (qubit ⊗ qubit))
    {q r s t : Fin 3 → ℝ}
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 = 1) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1) (ht : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 = 1) :
    ψ.expectation (pauliObservable q ⊗ pauliObservable s)
      + ψ.expectation (pauliObservable r ⊗ pauliObservable s)
      + ψ.expectation (pauliObservable r ⊗ pauliObservable t)
      - ψ.expectation (pauliObservable q ⊗ pauliObservable t) ≤ 2 * Real.sqrt 2 := sorry

end AxQM
