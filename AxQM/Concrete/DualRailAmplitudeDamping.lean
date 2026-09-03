/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Concrete: amplitude damping of a dual-rail qubit (N&C, Exercise 8.23)

The action of the tensor-product amplitude-damping channel `E_AD ⊗ E_AD` on the **dual-rail**
encoding of a qubit (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 8.23, p. 381).
-/

open scoped InnerProductSpace TensorProduct

open InnerProductSpace (rankOne)

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **dual-rail codeword** `|ψ⟩ = a|01⟩ + b|10⟩` (N&C eq. 8.113): a single excitation shared
between the two rails of the two-qubit space `H ⊗ H`, with amplitudes `a` for `|01⟩ = |0⟩⊗|1⟩` and
`c` for `|10⟩ = |1⟩⊗|0⟩`. -/
noncomputable def dualRailVec (a c : ℂ) : TensorProduct ℂ H H :=
  a • (b 0 ⊗ₜ[ℂ] b 1) + c • (b 1 ⊗ₜ[ℂ] b 0)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Error orthogonality**: the loss/error state `|00⟩` is orthogonal to every dual-rail codeword
`|ψ⟩ = a|01⟩ + b|10⟩`, i.e. `⟨00|ψ⟩ = 0`. Hence detecting the vacuum `|00⟩` (a "are there zero
photons?" measurement) flags an error without disturbing the surviving codewords — the dual-rail
error-detection principle (N&C §7.4, Exercise 8.23). -/
theorem dualRailVec_inner_ketZeroZero (a c : ℂ) :
    inner ℂ (b 0 ⊗ₜ[ℂ] b 0) (dualRailVec b a c) = 0 := sorry

/-- A single tensor operation element `E ⊗ F` of `E_AD ⊗ E_AD`, as a continuous linear map on the
two-qubit space, built from single-qubit operation elements `E, F : H →ₗ[ℂ] H` (the two-qubit space
is finite-dimensional, so each `LinearMap` bridges to a `ContinuousLinearMap`). -/
noncomputable def dualRailConjKraus (E F : H →ₗ[ℂ] H) :
    (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  TensorProduct.mapL (LinearMap.toContinuousLinearMap E) (LinearMap.toContinuousLinearMap F)

/-- The **dual-rail amplitude-damping process** `E_AD ⊗ E_AD` as an operator sum on density
operators: `ρ ↦ Σᵢⱼ (Eᵢ ⊗ Eⱼ) ρ (Eᵢ ⊗ Eⱼ)†` over the four tensor products of the single-qubit
operation elements `E₀, E₁` (N&C eqs. 8.107–8.108). -/
noncomputable def dualRailADChannel (γ : ℝ)
    (ρ : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H)) :
    (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausZero b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausZero b γ))))
    + (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausOne b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausOne b γ))))
    + (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausZero b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausZero b γ))))
    + (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausOne b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausOne b γ))))

omit [CompleteSpace H] in
/-- **The dual-rail error-detection process (N&C Exercise 8.23).** For a normalised dual-rail
codeword `|ψ⟩ = a|01⟩ + c|10⟩` (`‖a‖² + ‖c‖² = 1`) and `0 ≤ γ ≤ 1`, the tensor amplitude-damping
channel acts on the projector `|ψ⟩⟨ψ|` as
`E_AD ⊗ E_AD(|ψ⟩⟨ψ|) = (1-γ) |ψ⟩⟨ψ| + γ |00⟩⟨00|` —
*either nothing happens* (weight `1-γ`), *or* the excitation is lost and the state collapses to the
vacuum `|00⟩` (weight `γ`). -/
theorem dualRailADChannel_apply_dualRail (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a c : ℂ)
    (hnorm : ‖a‖ ^ 2 + ‖c‖ ^ 2 = 1) :
    dualRailADChannel b γ (rankOne ℂ (dualRailVec b a c) (dualRailVec b a c))
      = ((1 - γ : ℝ) : ℂ) • rankOne ℂ (dualRailVec b a c) (dualRailVec b a c)
        + (γ : ℂ) • rankOne ℂ (b 0 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 0) := sorry

/-- The **no-loss dual-rail operation element** `E₀ᵈʳ = √(1-γ) · I` (N&C eq. 8.114): `√(1-γ)` times
the identity on the two-qubit space `H ⊗ H` (it is basis-independent, so takes no basis
argument). -/
noncomputable def dualRailKrausZeroDR (γ : ℝ) :
    (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  (Real.sqrt (1 - γ) : ℂ) • ContinuousLinearMap.id ℂ (TensorProduct ℂ H H)

/-- The **first faithful reduced error element** `√γ |00⟩⟨01|`, sending the codeword
`a|01⟩ + c|10⟩` to `√γ·a |00⟩`. -/
noncomputable def dualRailErrZeroOne (γ : ℝ) : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  rankOne ℂ ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) (b 0 ⊗ₜ[ℂ] b 1)

/-- The **second faithful reduced error element** `√γ |00⟩⟨10|`, sending the codeword
`a|01⟩ + c|10⟩` to `√γ·c |00⟩`. -/
noncomputable def dualRailErrOneZero (γ : ℝ) : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  rankOne ℂ ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) (b 1 ⊗ₜ[ℂ] b 0)

omit [CompleteSpace H] in
/-- **Faithful completeness on the codespace.** The reduced dual-rail operation elements `{E₀ᵈʳ =
√(1-γ) I, √γ|00⟩⟨01|, √γ|00⟩⟨10|}` satisfy `Σ (Eᵏ)† Eᵏ = I` on the code: applied to any codeword
`|ψ⟩ = a|01⟩ + c|10⟩` the completeness operator returns `|ψ⟩`. -/
theorem dualRailFaithful_completeness (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a c : ℂ) :
    ((ContinuousLinearMap.adjoint (dualRailKrausZeroDR (H := H) γ)).comp (dualRailKrausZeroDR γ)
        + (ContinuousLinearMap.adjoint (dualRailErrZeroOne b γ)).comp (dualRailErrZeroOne b γ)
        + (ContinuousLinearMap.adjoint (dualRailErrOneZero b γ)).comp (dualRailErrOneZero b γ))
        (dualRailVec b a c)
      = dualRailVec b a c := sorry

/-- N&C's **single dual-rail error element** `E₁ᵈʳ = √γ (|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115): the
*coherent* sum of the two reduced loss elements. -/
noncomputable def dualRailErrCombined (γ : ℝ) : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  dualRailErrZeroOne b γ + dualRailErrOneZero b γ

omit [CompleteSpace H] in
/-- **Refutation of N&C's literal single-`E₁ᵈʳ` reading.** For `0 < γ ≤ 1`, N&C's `{E₀ᵈʳ, E₁ᵈʳ}`
completeness operator does not fix the codeword `|01⟩` (`Σ (Eᵏ)† Eᵏ ≠ I`): the single coherent
`E₁ᵈʳ = √γ(|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115) is **not** a trace-preserving operation-element
decomposition of `E_AD ⊗ E_AD` on the dual-rail code. -/
theorem dualRailErrCombined_not_completeness (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ((ContinuousLinearMap.adjoint (dualRailKrausZeroDR (H := H) γ)).comp (dualRailKrausZeroDR γ)
        + (ContinuousLinearMap.adjoint (dualRailErrCombined b γ)).comp (dualRailErrCombined b γ))
        (b 0 ⊗ₜ[ℂ] b 1)
      ≠ (b 0 ⊗ₜ[ℂ] b 1) := sorry

end AxQM.Concrete

end
