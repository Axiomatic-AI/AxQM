/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy

/-!
# N&C Exercise 11.18 — Equality in the concavity inequality (11.79)

*(N&C p. 517.)*

Prove equality in concavity inequality (11.79) iff all rho_i are the same.

* `vonNeumannEntropy_mix_eq_sum_iff_forall_eq`
-/

namespace AxQM

variable {S : QSystem}

/-- **Strict concavity of the von Neumann entropy** (Nielsen & Chuang **Exercise 11.18**, p. 517).
For a probability distribution `p` and a family of states `ρ : ι → State S`, equality holds in
the concavity inequality (11.79) `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`,

`S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ)`,

**iff all the components carrying positive weight are the same**, `∀ i j, 0 < pᵢ → 0 < pⱼ → ρ i
= ρ j`.

This is the literal form of the exercise's equality condition, that the `ρᵢ` all coincide; the
positive-weight guard is the exercise's own restriction to `pᵢ > 0` (a zero-weight component is
absent from the mixture and hence unconstrained).
-/
theorem State.vonNeumannEntropy_mix_eq_sum_iff_forall_eq {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy = ∑ i, p i * (ρ i).vonNeumannEntropy
      ↔ ∀ i j, 0 < p i → 0 < p j → ρ i = ρ j := sorry

end AxQM
