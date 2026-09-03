/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_14
import AxQM.NC.Ch9.Exercise9_17

/-!
# Nielsen & Chuang, Exercise 9.22 (Chaining property for fidelity measures)

*(N&C p. 418.)*

Chaining property for fidelity measures: E(VU,F∘E)<=E(U,E)+E(V,F).

* `gateChannelError` — the gate-approximation error `E(U, ℰ) = max_ρ d(U ρ U†, ℰ ρ)`;
* `gateChannelError_comp_le` — the chaining inequality `E(V U, ℱ ∘ ℰ) ≤ E(U, ℰ) + E(V, ℱ)`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The error of a channel `ℰ` approximating a unitary gate `U`, measured by a metric `d`**
(Nielsen & Chuang `(9.126)`): `E(U, ℰ) ≡ max_ρ d(U ρ U†, ℰ ρ)`, the largest metric distance
between the ideal evolved state `U ρ U†` (`Evolution.evolve`) and the actual output `ℰ ρ` over all
input states `ρ`. The maximum is realised as the supremum `⨆` over states. -/
noncomputable def gateChannelError (d : State S → State S → ℝ) (U : Evolution S)
    (E : State S → State S) : ℝ :=
  ⨆ ρ, d (U.evolve ρ) (E ρ)

/-- **Nielsen & Chuang, Exercise 9.22 — chaining property for fidelity measures.** For any metric
`d` on states satisfying the triangle inequality (`htriangle`) and unitary invariance
(`hunitary`, `d(W ρ W†, W σ W†) = d(ρ, σ)`), unitary gates `U, V`, and approximating operations
`ℰ, ℱ`, the error of the composite gate is at most the sum of the per-gate errors: `E(V U, ℱ ∘
ℰ) ≤ E(U, ℰ) + E(V, ℱ)`.

The boundedness hypotheses `hE`, `hF` and `[Nonempty (State S)]` are the well-definedness
conditions making the maxima genuine real numbers.
-/
theorem gateChannelError_comp_le [Nonempty (State S)]
    (d : State S → State S → ℝ)
    (htriangle : ∀ ρ σ τ : State S, d ρ τ ≤ d ρ σ + d σ τ)
    (hunitary : ∀ (W : Evolution S) (ρ σ : State S), d (W.evolve ρ) (W.evolve σ) = d ρ σ)
    (U V : Evolution S) (E F : State S → State S)
    (hE : BddAbove (Set.range fun ρ => d (U.evolve ρ) (E ρ)))
    (hF : BddAbove (Set.range fun σ => d (V.evolve σ) (F σ))) :
    gateChannelError d (V.comp U) (F ∘ E)
      ≤ gateChannelError d U E + gateChannelError d V F := sorry

end AxQM
