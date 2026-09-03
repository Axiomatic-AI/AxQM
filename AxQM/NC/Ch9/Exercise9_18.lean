/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_17
import AxQM.NC.Ch9.Theorem9_6

/-!
# Nielsen & Chuang, Exercise 9.18 (Contractivity of the angle)

*(N&C p. 414.)*

Show angle A(E(rho),E(sigma))<=A(rho,sigma) is contractive under quantum operation.

* `angle_channel_le`
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.18 (contractivity of the angle)**, `(9.91)`: a trace-preserving
quantum operation `f = E` never increases the angle between states, `A(E(ρ), E(σ)) ≤ A(ρ, σ)`. -/
theorem State.angle_channel_le {f : State S → State S} (hf : IsChannel f) (ρ σ : State S) :
    (f ρ).angle (f σ) ≤ ρ.angle σ := sorry

end AxQM
