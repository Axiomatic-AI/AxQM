/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.Normed.Algebra.LieTrotter

/-!
# AxQM.Basic.API — the symmetric (Strang) Trotter step (N&C Exercise 4.50(a))

The physics form of part (a) of Nielsen & Chuang, Exercise 4.50. Writing a
Hamiltonian as an ordered sum `H = Σₖ Hₖ` of Hamiltonians (each an `Observable`), the *symmetric*
(Strang) Trotter step is the **palindromic** product of the component propagators (N&C eq. 4.106).

## Main declarations
* `Observable.symmTrotterStep` — the palindromic `Evolution` product `U_Δt` above.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The symmetric (Strang) Trotter step** `U_Δt`.
Given a Hamiltonian decomposition into the list `Hs = [H₁, …, H_L]` (each an `Observable`) and a
step `Δt`, this is the **palindromic** `Evolution` product of the component propagators
`Hₖ.propagator 1 0 Δt = e^{-iHₖΔt}`. As a product of unitaries it is again a unitary
`Evolution`. -/
def Observable.symmTrotterStep (Hs : List (Observable S)) (Δt : ℝ) : Evolution S :=
  (Hs.map fun Hₖ => Hₖ.propagator 1 0 Δt).prod
    * (Hs.reverse.map fun Hₖ => Hₖ.propagator 1 0 Δt).prod

end AxQM
