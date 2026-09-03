/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HyperfineAngularMomentum
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: the coupled `|F, m_F⟩` hyperfine basis (Nielsen & Chuang, Exercise 7.28, part 2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.28 (p. 315) — the
"hyperfine states" exercise — couples a **nuclear spin `I = 3/2`** with an **electron spin
`S = 1/2`** into the total angular momentum `F = I + S` on `ℂ⁴ ⊗ ℂ² ≅ ℂ⁸`. Part 2 asks for the
simultaneous eigenvectors of `F² = f_x² + f_y² + f_z²` and `f_z`: the coupled `|F, m_F⟩` basis,
an `F = 2` quintet and an `F = 1` triplet.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The `F = 2`, `m_F = +2` hyperfine state `|2,+2⟩ = |m_I=+3/2, m_S=+½⟩ = e₆` (the stretched
state); Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2p2 : Fin 8 → ℂ := ![0, 0, 0, 0, 0, 0, 1, 0]

/-- The `F = 2`, `m_F = +1` hyperfine state `|2,+1⟩ = (√3/2)|+½,+½⟩ + (½)|+3/2,−½⟩ =
(√3/2) e₄ + (½) e₇`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2p1 : Fin 8 → ℂ :=
  ![0, 0, 0, 0, sqrt3 * 2⁻¹, 0, 0, 2⁻¹]

/-- The `F = 2`, `m_F = 0` hyperfine state `|2,0⟩ = (|−½,+½⟩ + |+½,−½⟩)/√2 = (e₂ + e₅)/√2`;
Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2z : Fin 8 → ℂ :=
  ![0, 0, invSqrt2, 0, 0, invSqrt2, 0, 0]

/-- The `F = 2`, `m_F = −1` hyperfine state `|2,−1⟩ = (½)|−3/2,+½⟩ + (√3/2)|−½,−½⟩ =
(½) e₀ + (√3/2) e₃`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2n1 : Fin 8 → ℂ :=
  ![2⁻¹, 0, 0, sqrt3 * 2⁻¹, 0, 0, 0, 0]

/-- The `F = 2`, `m_F = −2` hyperfine state `|2,−2⟩ = |m_I=−3/2, m_S=−½⟩ = e₁` (the stretched
state); Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2n2 : Fin 8 → ℂ := ![0, 1, 0, 0, 0, 0, 0, 0]

/-- The `F = 1`, `m_F = +1` hyperfine state `|1,+1⟩ = −(½)|+½,+½⟩ + (√3/2)|+3/2,−½⟩ =
−(½) e₄ + (√3/2) e₇`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF1p1 : Fin 8 → ℂ :=
  ![0, 0, 0, 0, -2⁻¹, 0, 0, sqrt3 * 2⁻¹]

/-- The `F = 1`, `m_F = 0` hyperfine state `|1,0⟩ = (|−½,+½⟩ − |+½,−½⟩)/√2 = (e₂ − e₅)/√2`;
Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF1z : Fin 8 → ℂ :=
  ![0, 0, invSqrt2, 0, 0, -invSqrt2, 0, 0]

/-- The `F = 1`, `m_F = −1` hyperfine state `|1,−1⟩ = (√3/2)|−3/2,+½⟩ − (½)|−½,−½⟩ =
(√3/2) e₀ − (½) e₃`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF1n1 : Fin 8 → ℂ :=
  ![sqrt3 * 2⁻¹, 0, 0, -2⁻¹, 0, 0, 0, 0]

/-- `f_z |2,+2⟩ = 2 |2,+2⟩`. -/
theorem hyperfineFz_mulVec_coupledF2p2 :
    hyperfineFz *ᵥ hyperfineCoupledF2p2 = (2 : ℂ) • hyperfineCoupledF2p2 := sorry

/-- `f_z |2,+1⟩ = 1 |2,+1⟩`. -/
theorem hyperfineFz_mulVec_coupledF2p1 :
    hyperfineFz *ᵥ hyperfineCoupledF2p1 = (1 : ℂ) • hyperfineCoupledF2p1 := sorry

/-- `f_z |2,0⟩ = 0`. -/
theorem hyperfineFz_mulVec_coupledF2z :
    hyperfineFz *ᵥ hyperfineCoupledF2z = (0 : ℂ) • hyperfineCoupledF2z := sorry

/-- `f_z |2,−1⟩ = −1 |2,−1⟩`. -/
theorem hyperfineFz_mulVec_coupledF2n1 :
    hyperfineFz *ᵥ hyperfineCoupledF2n1 = (-1 : ℂ) • hyperfineCoupledF2n1 := sorry

/-- `f_z |2,−2⟩ = −2 |2,−2⟩`. -/
theorem hyperfineFz_mulVec_coupledF2n2 :
    hyperfineFz *ᵥ hyperfineCoupledF2n2 = (-2 : ℂ) • hyperfineCoupledF2n2 := sorry

/-- `f_z |1,+1⟩ = 1 |1,+1⟩`. -/
theorem hyperfineFz_mulVec_coupledF1p1 :
    hyperfineFz *ᵥ hyperfineCoupledF1p1 = (1 : ℂ) • hyperfineCoupledF1p1 := sorry

/-- `f_z |1,0⟩ = 0`. -/
theorem hyperfineFz_mulVec_coupledF1z :
    hyperfineFz *ᵥ hyperfineCoupledF1z = (0 : ℂ) • hyperfineCoupledF1z := sorry

/-- `f_z |1,−1⟩ = −1 |1,−1⟩`. -/
theorem hyperfineFz_mulVec_coupledF1n1 :
    hyperfineFz *ᵥ hyperfineCoupledF1n1 = (-1 : ℂ) • hyperfineCoupledF1n1 := sorry

/-- `F² |2,+2⟩ = 6 |2,+2⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2p2 :
    hyperfineFSq *ᵥ hyperfineCoupledF2p2 = (6 : ℂ) • hyperfineCoupledF2p2 := sorry

/-- `F² |2,+1⟩ = 6 |2,+1⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2p1 :
    hyperfineFSq *ᵥ hyperfineCoupledF2p1 = (6 : ℂ) • hyperfineCoupledF2p1 := sorry

/-- `F² |2,0⟩ = 6 |2,0⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2z :
    hyperfineFSq *ᵥ hyperfineCoupledF2z = (6 : ℂ) • hyperfineCoupledF2z := sorry

/-- `F² |2,−1⟩ = 6 |2,−1⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2n1 :
    hyperfineFSq *ᵥ hyperfineCoupledF2n1 = (6 : ℂ) • hyperfineCoupledF2n1 := sorry

/-- `F² |2,−2⟩ = 6 |2,−2⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2n2 :
    hyperfineFSq *ᵥ hyperfineCoupledF2n2 = (6 : ℂ) • hyperfineCoupledF2n2 := sorry

/-- `F² |1,+1⟩ = 2 |1,+1⟩`: `F = 1`, so `F(F+1) = 2`. -/
theorem hyperfineFSq_mulVec_coupledF1p1 :
    hyperfineFSq *ᵥ hyperfineCoupledF1p1 = (2 : ℂ) • hyperfineCoupledF1p1 := sorry

/-- `F² |1,0⟩ = 2 |1,0⟩`: `F = 1`, so `F(F+1) = 2`. -/
theorem hyperfineFSq_mulVec_coupledF1z :
    hyperfineFSq *ᵥ hyperfineCoupledF1z = (2 : ℂ) • hyperfineCoupledF1z := sorry

/-- `F² |1,−1⟩ = 2 |1,−1⟩`: `F = 1`, so `F(F+1) = 2`. -/
theorem hyperfineFSq_mulVec_coupledF1n1 :
    hyperfineFSq *ᵥ hyperfineCoupledF1n1 = (2 : ℂ) • hyperfineCoupledF1n1 := sorry

/-- The change-of-basis matrix `U` whose columns are the eight coupled `|F, m_F⟩` states, ordered
`|2,−2⟩, |2,−1⟩, |2,0⟩, |2,+1⟩, |2,+2⟩, |1,−1⟩, |1,0⟩, |1,+1⟩` (the `F = 2` quintet by increasing
`m_F`, then the `F = 1` triplet). -/
noncomputable def hyperfineCoupledBasis : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 2⁻¹, 0, 0, 0, sqrt3 * 2⁻¹, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, invSqrt2, 0, 0, 0, invSqrt2, 0;
     0, sqrt3 * 2⁻¹, 0, 0, 0, -2⁻¹, 0, 0;
     0, 0, 0, sqrt3 * 2⁻¹, 0, 0, 0, -2⁻¹;
     0, 0, invSqrt2, 0, 0, 0, -invSqrt2, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 2⁻¹, 0, 0, 0, sqrt3 * 2⁻¹]

set_option maxRecDepth 4000 in -- entrywise unfolding of an explicit `8 × 8` matrix product
/-- The coupled basis is **orthonormal**: `Uᴴ U = I`. -/
theorem hyperfineCoupledBasis_conjTranspose_mul_self :
    hyperfineCoupledBasisᴴ * hyperfineCoupledBasis = 1 := sorry

end AxQM.Concrete
