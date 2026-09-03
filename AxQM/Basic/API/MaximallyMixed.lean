/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# AxQM.Basic.API — the maximally mixed state `I/d`

The **maximally mixed state** of a quantum system `S`: the density operator `I/d` where
`d = dim S` is the dimension of the state space. It is the state of maximal von Neumann entropy —
"total ignorance" — and the reduced state of a maximally entangled bipartite pure state
(Nielsen & Chuang §2.4.3; the `I/2` of Exercise 2.75).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **maximally mixed state** `I/d` of the system `S`, where `d = dim S`: the density operator
`(finrank ℂ S.space)⁻¹ • 1`. Requires `Nontrivial S.space` (a state needs a nontrivial space). This
is the state of maximal entropy, and the marginal of a maximally entangled pure state. -/
def maximallyMixedState (S : QSystem) [Nontrivial S.space] : State S where
  op := (Module.finrank ℂ S.space : ℂ)⁻¹ • 1
  isDensity := ContinuousLinearMap.isDensityOp_finrank_inv_smul_one

end AxQM
