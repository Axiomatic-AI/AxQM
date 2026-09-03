/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.ModularMultiplication
import Mathlib.Data.Matrix.PEquiv

/-!
# Temporal labeling: the population-permutation circuit (Nielsen & Chuang, Exercise 7.42)

*Temporal labeling* (§7.7.1, p. 333) prepares an *effective* pure state on an NMR ensemble by
summing the traceless observables of three experiments run on permuted copies of the thermal state.
The two permutations are performed by a small circuit `P` of controlled-NOT gates, acting on the
diagonal two-spin density matrix of N&C (7.153).
-/

namespace AxQM.Concrete

open Matrix

/-- **`ρ₁` of N&C (7.153)**: the diagonal two-spin density matrix with populations `(a, b, c, d)` on
the big-endian computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
noncomputable def temporalLabelRho1 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, b, c, d]

/-- **`ρ₂` of N&C (7.154)**: the populations cyclically permuted to `(a, c, d, b)`, the state
`P ρ₁ P†` obtained by the temporal-labeling circuit. -/
noncomputable def temporalLabelRho2 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, c, d, b]

/-- **`ρ₃` of N&C (7.155)**: the populations cyclically permuted to `(a, d, b, c)`, the state
`P† ρ₁ P` obtained by the inverse circuit. -/
noncomputable def temporalLabelRho3 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, d, b, c]

/-- The **`CNOT` gate matrix with the second qubit as control** (target = first qubit): the basis
permutation swapping `|01⟩ ↔ |11⟩` (indices `1 ↔ 3` in big-endian order), i.e. `|q₀ q₁⟩ ↦ |q₀ ⊕
q₁, q₁⟩`. -/
noncomputable def cnotSecondControlMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if Equiv.swap 1 3 i = j then 1 else 0

/-- The **temporal-labeling permutation circuit `P`** (N&C, Exercise 7.42). As a matrix product the
later gate is on the left. -/
noncomputable def temporalLabelCircuit : Matrix (Fin 4) (Fin 4) ℂ :=
  cnotSecondControlMatrix * cnotMatrix

/-- **Exercise 7.42, the permutation `P` (N&C 7.154):** `P ρ₁ P† = ρ₂`, i.e. the circuit conjugation
sends the populations `(a, b, c, d)` to `(a, c, d, b)`. -/
theorem temporalLabelCircuit_conj_temporalLabelRho1 (a b c d : ℂ) :
    temporalLabelCircuit * temporalLabelRho1 a b c d * temporalLabelCircuitᴴ
      = temporalLabelRho2 a b c d := sorry

/-- **Exercise 7.42, the adjoint permutation `P†` (N&C 7.155):** `P† ρ₁ P = ρ₃`, i.e. the inverse
circuit sends the populations `(a, b, c, d)` to `(a, d, b, c)`. -/
theorem temporalLabelCircuit_conjTranspose_conj_temporalLabelRho1 (a b c d : ℂ) :
    temporalLabelCircuitᴴ * temporalLabelRho1 a b c d * temporalLabelCircuit
      = temporalLabelRho3 a b c d := sorry

end AxQM.Concrete
