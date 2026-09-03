/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyComposite

/-!
# AxQM — the equality case of the von Neumann entropy bound

Nielsen & Chuang, Theorem 11.8, part (2): in a `d`-dimensional space the von Neumann entropy
satisfies `S(ρ) ≤ log d`, **with equality if and only if `ρ` is the maximally mixed state `I/d`**.

## Main results

* `AxQM.State.vonNeumannEntropy_eq_log_finrank_iff_eq_maximallyMixed` — the full equality
  characterization `S(ρ) = log d ↔ ρ = I/d`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Full equality characterization of the von Neumann entropy bound** (Nielsen & Chuang,
Theorem 11.8, part (2)): the entropy of a state attains its maximum `S(ρ) = log d`
(`d = dim S.space`) if and only if `ρ` is the maximally mixed state `I/d`. -/
theorem State.vonNeumannEntropy_eq_log_finrank_iff_eq_maximallyMixed [Nontrivial S.space]
    (ρ : State S) :
    ρ.vonNeumannEntropy = Real.log (Module.finrank ℂ S.space : ℝ) ↔ ρ = maximallyMixedState S :=
      sorry

end AxQM
