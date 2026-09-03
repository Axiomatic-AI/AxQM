/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Concrete: two-level decomposition of the 4×4 quantum Fourier transform (N&C Ex 4.37)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.37 (p. 191) asks
for a decomposition of the `4 × 4` quantum Fourier transform (eq. 4.52) into two-level unitaries.

## The decomposition

* `qftFactorH02` — `H` on the coordinate pair `{0,2}` (identity on `{1,3}`);
* `qftFactorG13` — `G` on `{1,3}` (identity on `{0,2}`);
* `qftFactorH01` — `H` on `{0,1}`;
* `qftFactorH23` — `H` on `{2,3}`;
* `qftFactorSwap` — the transposition (bit-reversal swap) of `{1,2}`.
-/

namespace AxQM.Concrete

open Matrix

/-- A `d × d` complex matrix `U` is a **two-level unitary** (Nielsen & Chuang §4.5.1) when it is
unitary and acts non-trivially on at most two computational basis vectors: there are indices
`p, q` such that `U` agrees with the identity on every entry lying outside the `{p,q} × {p,q}`
principal submatrix. Allowing `p = q` includes the one-level (single-phase) case, so this captures
"acts non-trivially on two-or-fewer components". -/
def IsTwoLevelUnitary {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
    ∃ p q : Fin d, ∀ i j : Fin d,
      (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q) → U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j

/-- The 4×4 quantum Fourier transform `F` of Nielsen & Chuang eq. (4.52), `Fⱼₖ = ½ · iʲᵏ`:
`½ !![1,1,1,1; 1,i,-1,-i; 1,-1,1,-1; 1,-i,-1,i]`. This is the `N = 4` discrete Fourier transform
matrix, i.e. the two-qubit QFT. -/
noncomputable def qftFour : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![1, 1, 1, 1; 1, Complex.I, -1, -Complex.I;
     1, -1, 1, -1; 1, -Complex.I, -1, Complex.I]

/-- First factor: the Hadamard block `H = (√2)⁻¹ !![1,1; 1,-1]` acting on the coordinate pair
`{0,2}`, identity on `{1,3}`. A two-level unitary. -/
noncomputable def qftFactorH02 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, 0, (Real.sqrt 2 : ℂ)⁻¹, 0; 0, 1, 0, 0;
     (Real.sqrt 2 : ℂ)⁻¹, 0, -(Real.sqrt 2 : ℂ)⁻¹, 0; 0, 0, 0, 1]

/-- Second factor: the twiddled Hadamard block `G = (√2)⁻¹ !![1,i; 1,-i]` acting on the coordinate
pair `{1,3}`, identity on `{0,2}`. A two-level unitary. -/
noncomputable def qftFactorG13 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, (Real.sqrt 2 : ℂ)⁻¹, 0, Complex.I * (Real.sqrt 2 : ℂ)⁻¹;
     0, 0, 1, 0; 0, (Real.sqrt 2 : ℂ)⁻¹, 0, -(Complex.I * (Real.sqrt 2 : ℂ)⁻¹)]

/-- Third factor: the Hadamard block `H = (√2)⁻¹ !![1,1; 1,-1]` acting on the coordinate pair
`{0,1}`, identity on `{2,3}`. A two-level unitary. -/
noncomputable def qftFactorH01 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹, 0, 0;
     (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Fourth factor: the Hadamard block `H = (√2)⁻¹ !![1,1; 1,-1]` acting on the coordinate pair
`{2,3}`, identity on `{0,1}`. A two-level unitary. -/
noncomputable def qftFactorH23 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, (Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹;
     0, 0, (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- Fifth factor: the transposition (bit-reversal swap) of the coordinate pair `{1,2}`, identity on
`{0,3}`. A two-level unitary (a permutation matrix). -/
def qftFactorSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

/-- **Nielsen & Chuang, Exercise 4.37.** The 4×4 quantum Fourier transform factors as a product of
five two-level unitaries, `F = qftFactorH02 · qftFactorG13 · qftFactorH01 · qftFactorH23 ·
qftFactorSwap`. -/
theorem qftFour_eq_prod :
    qftFour = qftFactorH02 * qftFactorG13 * qftFactorH01 * qftFactorH23 * qftFactorSwap := sorry

/-- The first factor is a two-level unitary, acting only on `{0,2}`. -/
theorem qftFactorH02_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorH02 := sorry

/-- The second factor is a two-level unitary, acting only on `{1,3}`. -/
theorem qftFactorG13_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorG13 := sorry

/-- The third factor is a two-level unitary, acting only on `{0,1}`. -/
theorem qftFactorH01_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorH01 := sorry

/-- The fourth factor is a two-level unitary, acting only on `{2,3}`. -/
theorem qftFactorH23_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorH23 := sorry

/-- The fifth factor is a two-level unitary, acting only on `{1,2}` (a transposition). -/
theorem qftFactorSwap_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorSwap := sorry

end AxQM.Concrete
