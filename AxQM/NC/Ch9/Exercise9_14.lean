/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_6
import AxQM.Basic.API.RandomUnitaryChannel

/-!
# Nielsen & Chuang, Exercise 9.14 (Invariance of fidelity under unitary transforms)

*(N&C p. 410.)*

Prove fidelity invariance under unitary transforms F(UrhoU†,UsigmaU†)=F(rho,sigma).

* `fidelity_evolve` — `F(U ρ U†, U σ U†) = F(ρ, σ)` for every unitary evolution `U` and all states
  `ρ, σ`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.14 — invariance of the fidelity under unitary transforms**
(`(9.61)`).
-/
theorem State.fidelity_evolve (U : Evolution S) (ρ σ : State S) :
    (U.evolve ρ).fidelity (U.evolve σ) = ρ.fidelity σ := sorry

end AxQM
