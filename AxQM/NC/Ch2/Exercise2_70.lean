/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellBasis

/-!
# Nielsen & Chuang, Exercise 2.70 (Bell states are locally indistinguishable)

*(N&C p. 98.)*

Show <psi|E⊗I|psi> is same for all four Bell states; can Eve infer Alice's bits?

* `bellState_expectation_tmul_id_eq` — `⟪E⊗I⟫_{β_xy} = ⟪E⊗I⟫_{β_x'y'}` for all `x, y, x', y'` — the
  expectation is the same for all four Bell states.
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.70.** For any observable `E` on Alice's qubit, the one-sided
expectation `⟪E ⊗ I⟫` takes the *same* value in every Bell state `|β_xy⟩` (N&C eq.
(2.134)–(2.137)): `⟪E⊗I⟫_{β_xy} = ⟪E⊗I⟫_{β_x'y'}` for all `x, y, x', y'`. Hence Eve, who
intercepts only Alice's qubit in the superdense coding protocol, sees Bell-state-independent
statistics and can infer nothing about Alice's two bits.
-/
theorem bellState_expectation_tmul_id_eq (E : Observable qubit) (x y x' y' : Fin 2) :
    (bellState x y).expectation (E ⊗ Observable.id qubit)
      = (bellState x' y').expectation (E ⊗ Observable.id qubit) := sorry

end AxQM
