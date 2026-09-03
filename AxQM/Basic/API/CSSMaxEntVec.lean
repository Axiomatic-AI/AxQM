/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CSSPhaseBasis
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi

/-!
# The `n` EPR pairs expressed in the CSS state basis (Nielsen & Chuang, Exercise 12.36)

Nielsen & Chuang, Exercise 12.36 (p. 598), asks to **verify Equation (12.203)**.
-/

open scoped Matrix InnerProductSpace TensorProduct

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- The **(unnormalised) maximally entangled vector of the `n` EPR pairs** `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩ ⊗ |j⟩`,
an element of `(bitReg ι).space ⊗ (bitReg ι).space` — the first factor holds the `n` qubits Alice
keeps, the second the `n` qubits sent to Bob (Nielsen & Chuang eq. (12.203), left/middle). The
normalised `n`-EPR state is `2^{-n/2}` times this. -/
noncomputable def nEPRVec (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (bitReg ι).space ⊗[ℂ] (bitReg ι).space :=
  (regBasis ι).maxEntVec

/-- **First equality of Eq. (12.203):** `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩ ⊗ |j⟩`, the sum over the computational
basis `{|w⟩}` of `|w⟩ ⊗ |w⟩`. -/
theorem nEPRVec_eq_sum_regBasis_tmul :
    nEPRVec ι = ∑ w : ι → ZMod 2, regBasis ι w ⊗ₜ[ℂ] regBasis ι w := sorry

/-- **Equation (12.203) in full:** the `n`-EPR maximally entangled vector expanded in the CSS
phase-coset basis, `|β₀₀⟩⊗ⁿ = ∑_{v_k,z,x} |ξ_{v_k,z,x}⟩ ⊗ |ξ_{v_k,z,x}⟩`. -/
theorem nEPRVec_eq_sum_cssPhaseFamily_tmul :
    nEPRVec ι = ∑ p : cssPhaseIndex C₂, cssPhaseFamily C₂ p ⊗ₜ[ℂ] cssPhaseFamily C₂ p := sorry

end AxQM
