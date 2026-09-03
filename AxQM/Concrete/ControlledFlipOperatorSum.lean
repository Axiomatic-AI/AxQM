/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QubitBasisOperators
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Concrete: operator-sum representation of the controlled-flip channel (N&C Exercise 8.4)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 8.4** (p. 361): a
single-qubit *principal system* interacts with a single-qubit *environment* through the
controlled-flip unitary `U = P₀ ⊗ I + P₁ ⊗ X`, and the quantum operation this induces on the
principal system is asked for in operator-sum form.
-/

open scoped TensorProduct InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **controlled-flip interaction** `U = P₀ ⊗ I + P₁ ⊗ X` (N&C eq. 8.16): a CNOT with the
principal system controlling the environment's bit-flip. -/
noncomputable def controlledFlip : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  TensorProduct.map (qubitProj b 0) LinearMap.id + TensorProduct.map (qubitProj b 1) (qubitFlip b)

/-- The **dilation** `V = U (· ⊗ |0⟩) : H →ₗ H ⊗ H`. -/
noncomputable def controlledFlipDilation : H →ₗ[ℂ] H ⊗[ℂ] H :=
  controlledFlip b ∘ₗ LinearMap.embedRight b 0

/-- The **quantum operation** of Exercise 8.4, in environment form `E(ρ) = tr_env(V ρ V†)`
with `V ρ V† = U (ρ ⊗ |0⟩⟨0|) U†`. -/
noncomputable def dephasingOperation (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (controlledFlipDilation b ∘ₗ ρ ∘ₗ LinearMap.adjoint (controlledFlipDilation b))

/-- **Operator-sum representation (N&C eq. 8.7):** the quantum operation of Exercise 8.4 is `E(ρ) =
P₀ ρ P₀ + P₁ ρ P₁`, the completely dephasing channel. -/
theorem dephasingOperation_eq_operatorSum (ρ : H →ₗ[ℂ] H) :
    dephasingOperation b ρ =
      qubitProj b 0 ∘ₗ ρ ∘ₗ qubitProj b 0 + qubitProj b 1 ∘ₗ ρ ∘ₗ qubitProj b 1 := sorry

end AxQM.Concrete
