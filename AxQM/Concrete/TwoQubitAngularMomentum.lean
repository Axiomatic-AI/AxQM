/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliKronecker
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: total angular momentum of two spin-½ particles (Nielsen & Chuang, Exercise 7.26)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.26 (p. 314)
asks to **verify the properties of the coupled states `|j, m_j⟩_J`** — that they are
simultaneous eigenstates of `J²` and `j_z` — by explicitly writing the `4 × 4` matrices
`J²` and `j_z` in the basis they define.

## Contents

* `totalJx`, `totalJy`, `totalJz`, `totalJSq` — the four operators as `4 × 4` matrices,
  built from the Pauli matrices by Kronecker product, with their explicit matrix forms
  `totalJz_eq` and `totalJSq_eq`. In particular
  `totalJz = diag(1, 0, 0, −1)` and
  `totalJSq = !![2,0,0,0; 0,1,1,0; 0,1,1,0; 0,0,0,2]` — the two matrices the exercise asks
  us to write out.
* `coupledSinglet`, `coupledTripletPlus`, `coupledTripletZero`, `coupledTripletMinus` — the
  four coupled-basis vectors.
* `..._mulVec_...` (eight theorems) — the **properties to verify**: each coupled state is an
  eigenvector of `J²` with eigenvalue `j(j+1)` (`0` for the singlet, `2` for the triplet)
  and simultaneously of `j_z` with its `j_z`-eigenvalue. Column by column these say exactly
  that `J²` and `j_z` are **diagonal in the coupled basis** with entries `(0,2,2,2)` and
  `(0,1,0,−1)`.
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped Kronecker

/-- The total angular-momentum `x`-operator `j_x = (X ⊗ I + I ⊗ X)/2` of two spin-½ particles,
as a `4 × 4` matrix in the computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
noncomputable def totalJx : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • flattenFin4 (pauliX ⊗ₖ pauliI + pauliI ⊗ₖ pauliX)

/-- The total angular-momentum `y`-operator `j_y = (Y ⊗ I + I ⊗ Y)/2`. -/
noncomputable def totalJy : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • flattenFin4 (pauliY ⊗ₖ pauliI + pauliI ⊗ₖ pauliY)

/-- The total angular-momentum `z`-operator `j_z = (Z ⊗ I + I ⊗ Z)/2`. -/
noncomputable def totalJz : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • flattenFin4 (pauliZ ⊗ₖ pauliI + pauliI ⊗ₖ pauliZ)

/-- The total angular-momentum-squared operator `J² = j_x² + j_y² + j_z²` (N&C (7.97)). -/
noncomputable def totalJSq : Matrix (Fin 4) (Fin 4) ℂ :=
  totalJx * totalJx + totalJy * totalJy + totalJz * totalJz

/-- The explicit matrix of `j_z = (Z₁ + Z₂)/2`: the diagonal matrix `diag(1, 0, 0, −1)`. This is
one of the two matrices Nielsen & Chuang, Exercise 7.26 asks us to write out. -/
theorem totalJz_eq :
    totalJz = !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1] := sorry

/-- The explicit matrix of `J² = j_x² + j_y² + j_z²`:
`!![2,0,0,0; 0,1,1,0; 0,1,1,0; 0,0,0,2]`. This is the second matrix Nielsen & Chuang,
Exercise 7.26 asks us to write out; it is block-diagonal (not diagonal) in the computational
basis. -/
theorem totalJSq_eq :
    totalJSq = !![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 2] := sorry

/-- The spin **singlet** `|0,0⟩_J = (|01⟩ − |10⟩)/√2` (N&C (7.93)); total angular momentum
`j = 0`, `m_j = 0`. -/
noncomputable def coupledSinglet : Fin 4 → ℂ := ![0, invSqrt2, -invSqrt2, 0]

/-- The triplet state `|00⟩` (N&C (7.94), labelled `|1,−1⟩_J`); `j = 1`, and a `j_z`-eigenstate
with eigenvalue `+1` under the standard `Z = diag(1,−1)` convention. -/
noncomputable def coupledTripletPlus : Fin 4 → ℂ := ![1, 0, 0, 0]

/-- The triplet state `|1,0⟩_J = (|01⟩ + |10⟩)/√2` (N&C (7.95)); `j = 1`, `m_j = 0`. -/
noncomputable def coupledTripletZero : Fin 4 → ℂ := ![0, invSqrt2, invSqrt2, 0]

/-- The triplet state `|11⟩` (N&C (7.96), labelled `|1,1⟩_J`); `j = 1`, and a `j_z`-eigenstate
with eigenvalue `−1` under the standard `Z = diag(1,−1)` convention. -/
noncomputable def coupledTripletMinus : Fin 4 → ℂ := ![0, 0, 0, 1]

/-- `j_z |0,0⟩_J = 0`: the singlet has `m_j = 0`. -/
theorem totalJz_mulVec_coupledSinglet :
    totalJz *ᵥ coupledSinglet = (0 : ℂ) • coupledSinglet := sorry

/-- `j_z |00⟩ = +|00⟩`: eigenvalue `+1` (N&C's `|1,−1⟩_J`). -/
theorem totalJz_mulVec_coupledTripletPlus :
    totalJz *ᵥ coupledTripletPlus = (1 : ℂ) • coupledTripletPlus := sorry

/-- `j_z |1,0⟩_J = 0`: the symmetric triplet state has `m_j = 0`. -/
theorem totalJz_mulVec_coupledTripletZero :
    totalJz *ᵥ coupledTripletZero = (0 : ℂ) • coupledTripletZero := sorry

/-- `j_z |11⟩ = −|11⟩`: eigenvalue `−1` (N&C's `|1,1⟩_J`). -/
theorem totalJz_mulVec_coupledTripletMinus :
    totalJz *ᵥ coupledTripletMinus = (-1 : ℂ) • coupledTripletMinus := sorry

/-- `J² |0,0⟩_J = 0`: the singlet has `j = 0`, so `J²`-eigenvalue `j(j+1) = 0`. -/
theorem totalJSq_mulVec_coupledSinglet :
    totalJSq *ᵥ coupledSinglet = (0 : ℂ) • coupledSinglet := sorry

/-- `J² |00⟩ = 2|00⟩`: the triplet has `j = 1`, so `J²`-eigenvalue `j(j+1) = 2`. -/
theorem totalJSq_mulVec_coupledTripletPlus :
    totalJSq *ᵥ coupledTripletPlus = (2 : ℂ) • coupledTripletPlus := sorry

/-- `J² |1,0⟩_J = 2|1,0⟩_J`: `j = 1`, `J²`-eigenvalue `2`. -/
theorem totalJSq_mulVec_coupledTripletZero :
    totalJSq *ᵥ coupledTripletZero = (2 : ℂ) • coupledTripletZero := sorry

/-- `J² |11⟩ = 2|11⟩`: `j = 1`, `J²`-eigenvalue `2`. -/
theorem totalJSq_mulVec_coupledTripletMinus :
    totalJSq *ᵥ coupledTripletMinus = (2 : ℂ) • coupledTripletMinus := sorry

end AxQM.Concrete
