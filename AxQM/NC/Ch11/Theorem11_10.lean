/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.Entropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.Basic.API.MaximallyMixed
import AxQM.NC.Ch11.Theorem11_6
import AxQM.NC.Ch9.Theorem9_3

/-!
# N&C Theorem 11.10 — Entropy of a mixture of quantum states

*(N&C p. 518.)*

Entropy of a mixture: S(rho)<=sum p_i S(rho_i)+H(p_i), equality iff orthogonal supports.

* `vonNeumannEntropy_mix_le'` — the general (faithfulness-free) upper bound `S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ
  S(ρᵢ) + H(p)` for an arbitrary family of states, i.e. eq. (11.87) exactly as N&C state it (no
  strict-positivity hypothesis).
-/

namespace AxQM

open Filter
open scoped Topology

variable {S : QSystem}

/-- **Entropy of a mixture — upper bound, general form** (Nielsen & Chuang, Theorem 11.10, eq.
(11.87)). For *any* probability distribution `p` and *any* family `ρ : ι → State S` of quantum
states, the von Neumann entropy of the mixture is bounded by the average component entropy plus
the Shannon entropy of the weights:

`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`.

This is eq. (11.87) exactly as N&C state it, with no strict-positivity restriction on the states.
-/
theorem State.vonNeumannEntropy_mix_le' {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      ≤ ∑ i, p i * (ρ i).vonNeumannEntropy + Real.entropy p := sorry

end AxQM
