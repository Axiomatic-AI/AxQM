/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Concrete: computational-basis operators on an abstract qubit

Reusable operators on an arbitrary two-dimensional complex inner product space `H`
(a qubit) equipped with a chosen computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`:
the projectors `Pᵢ = |i⟩⟨i|`, the Pauli bit-flip `X = |0⟩⟨1| + |1⟩⟨0|`, and the lowering operator
`σ₋ = |0⟩⟨1|` (its adjoint `σ₊ = |1⟩⟨0|` the raising operator).
-/

open scoped InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

variable (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The computational-basis **projector** `Pᵢ = |i⟩⟨i|` of the qubit, as the bare `LinearMap`
coercion of `InnerProductSpace.rankOne ℂ (b i) (b i)`. -/
noncomputable def qubitProj (i : Fin 2) : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b i) (b i) : H →ₗ[ℂ] H)

/-- The qubit **bit-flip** (Pauli `X`) operator `X = |0⟩⟨1| + |1⟩⟨0|`. -/
noncomputable def qubitFlip : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b 0) (b 1) : H →ₗ[ℂ] H)
    + (InnerProductSpace.rankOne ℂ (b 1) (b 0) : H →ₗ[ℂ] H)

/-- The atomic **lowering operator** `σ₋ = |0⟩⟨1|` of the qubit (N&C §8.4.1): it sends the excited
state `|1⟩` to the ground state `|0⟩` and annihilates `|0⟩`. As the bare `LinearMap` coercion of
`InnerProductSpace.rankOne ℂ (b 0) (b 1)`. -/
noncomputable def qubitLower : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b 0) (b 1) : H →ₗ[ℂ] H)

/-- The computational-basis **matrix unit** `|i⟩⟨j|` of the qubit, as the bare `LinearMap` coercion
of `InnerProductSpace.rankOne ℂ (b i) (b j)`. -/
noncomputable def qubitUnit (i j : Fin 2) : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b i) (b j) : H →ₗ[ℂ] H)

/-- The qubit **Pauli `Z`** operator `Z = |0⟩⟨0| - |1⟩⟨1| = P₀ - P₁`, the difference of the two
computational-basis projectors. -/
noncomputable def qubitPauliZ : H →ₗ[ℂ] H := qubitProj b 0 - qubitProj b 1

/-- The rank-one projector `|+⟩⟨+| = ½(I + X)` onto the `+1`-eigenvector of the bit-flip `X`. -/
noncomputable def qubitPlusProj : H →ₗ[ℂ] H := (2 : ℂ)⁻¹ • (LinearMap.id + qubitFlip b)

/-- The rank-one projector `|-⟩⟨-| = ½(I - X)` onto the `-1`-eigenvector of the bit-flip `X`. -/
noncomputable def qubitMinusProj : H →ₗ[ℂ] H := (2 : ℂ)⁻¹ • (LinearMap.id - qubitFlip b)

end AxQM.Concrete
