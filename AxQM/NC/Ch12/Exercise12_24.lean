/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.StateMajorization
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.Support
import Mathlib.Analysis.InnerProductSpace.Positive
import AxQM.NC.Ch2.Problem2_2

/-!
# Nielsen–Chuang, Exercise 12.24 — the Schmidt number is LOCC-monotone

*(N&C p. 580.)*

Schmidt number cannot be increased by LOCC; Bell-state count non-increasing.

* `schmidtNumber_le_of_reducedLeft_loccConvertible` — the Schmidt number cannot be increased by
  LOCC. If `|ψ⟩` can be converted to `|φ⟩` by one-way LOCC — encoded, as in Nielsen's theorem, by
  `ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft` (Alice's measurement carrying her
  marginal `ρ_ψ` to `ρ_φ`) — then `φ.schmidtNumber ≤ ψ.schmidtNumber`.
* `bellCount_le_of_reducedLeft_loccConvertible` — the number of Bell states cannot be increased by
  LOCC. A shared resource of `k` Bell pairs is a bipartite pure state of Schmidt number `2 ^ k`.
-/

namespace AxQM

namespace PureState

variable {S T : QSystem}

/-- **The Schmidt number cannot be increased by LOCC** (Nielsen–Chuang, Exercise 12.24, part 1). If
the bipartite pure state `|ψ⟩` can be converted to `|φ⟩` by one-way LOCC — encoded via Nielsen's
theorem as convertibility of Alice's reduced states, `ψ.toState.reducedLeft.LOCCConvertible
φ.toState.reducedLeft` — then the Schmidt number does not increase: `φ.schmidtNumber ≤
ψ.schmidtNumber`.
-/
theorem schmidtNumber_le_of_reducedLeft_loccConvertible {ψ φ : PureState (S.compose T)}
    (h : ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft) :
    φ.schmidtNumber ≤ ψ.schmidtNumber := sorry

/-- **The number of Bell states cannot be increased by LOCC** (Nielsen–Chuang, Exercise 12.24, part
2). So if `ψ` carries `m` Bell pairs (`ψ.schmidtNumber = 2 ^ m`) and `φ` carries `n`
(`φ.schmidtNumber = 2 ^ n`), and `|ψ⟩` can be converted to `|φ⟩` by LOCC, then `n ≤ m`: the
Bell-pair count is non-increasing. -/
theorem bellCount_le_of_reducedLeft_loccConvertible {ψ φ : PureState (S.compose T)} {m n : ℕ}
    (hψ : ψ.schmidtNumber = 2 ^ m) (hφ : φ.schmidtNumber = 2 ^ n)
    (h : ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft) :
    n ≤ m := sorry

end PureState

end AxQM
