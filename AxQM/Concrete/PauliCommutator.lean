/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Analysis.Complex.Basic

/-!
# Concrete: multiplication and commutation relations for the Pauli matrices (N&C Ex. 2.40, 2.43)

The Pauli-matrix commutation relations of Nielsen & Chuang, Exercise 2.40, and the full
multiplication relation of Exercise 2.43, over the `2 × 2` complex matrices `pauliX`, `pauliY`,
`pauliZ`.

## Declarations

* `leviCivita3` — the totally antisymmetric symbol `ε` on three `Fin 3` indices, `+1` on the
  cyclic orderings, `-1` on the anticyclic ones, `0` when any two indices coincide.
* `pauliSigma` — the family `σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` indexing the three
  non-identity Pauli matrices.
* `pauliSigma_lie` — the elegant commutator tensor form (eq. 2.74): `⁅σⱼ, σₖ⁆ = 2i Σₗ ε_{jkl} σₗ`.
* `pauliSigma_mul` — the full multiplication relation (Exercise 2.43, eq. 2.78):
  `σⱼ σₖ = δ_{jk} I + i Σₗ ε_{jkl} σₗ`.
* `pauliX_lie_pauliY`, `pauliY_lie_pauliZ`, `pauliZ_lie_pauliX` — the three explicit relations (eq.
  2.73).
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The totally antisymmetric Levi-Civita symbol `ε` on three `Fin 3` indices (Nielsen & Chuang, eq.
2.74). It is `+1` on the cyclic orderings `(0,1,2), (1,2,0), (2,0,1)`, `-1` on the anticyclic
orderings `(2,1,0), (1,0,2), (0,2,1)`, and `0` whenever two indices coincide. -/
def leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- The family `σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` indexing the three non-identity Pauli
matrices: `pauliSigma 0 = X`, `pauliSigma 1 = Y`, `pauliSigma 2 = Z` (N&C's `σ₁, σ₂, σ₃`). -/
def pauliSigma : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliX, pauliY, pauliZ]

/-- **Commutation relations for the Pauli matrices, elegant form** (Nielsen & Chuang, Exercise 2.40,
eq. 2.74): `⁅σⱼ, σₖ⁆ = 2i Σₗ ε_{jkl} σₗ`, where `⁅·,·⁆` is the matrix commutator `AB − BA`. -/
theorem pauliSigma_lie (j k : Fin 3) :
    ⁅pauliSigma j, pauliSigma k⁆ =
      (2 * I) • ∑ l, (leviCivita3 j k l : ℂ) • pauliSigma l := sorry

/-- **Full multiplication relation for the Pauli matrices** (Nielsen & Chuang, Exercise 2.43, eq.
2.78): for `j, k = 1, 2, 3`, `σⱼ σₖ = δ_{jk} I + i Σₗ ε_{jkl} σₗ`, where `δ_{jk}` is the
Kronecker delta (here `if j = k then 1 else 0`) and `I` the identity matrix. -/
theorem pauliSigma_mul (j k : Fin 3) :
    pauliSigma j * pauliSigma k =
      (if j = k then (1 : ℂ) else 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + I • ∑ l, (leviCivita3 j k l : ℂ) • pauliSigma l := sorry

/-- **`[X, Y] = 2iZ`** (Nielsen & Chuang, Exercise 2.40, eq. 2.73), i.e. `⁅σ₁, σ₂⁆ = 2i σ₃`. -/
theorem pauliX_lie_pauliY : ⁅pauliX, pauliY⁆ = (2 * I) • pauliZ := sorry

/-- **`[Y, Z] = 2iX`** (Nielsen & Chuang, Exercise 2.40, eq. 2.73), i.e. `⁅σ₂, σ₃⁆ = 2i σ₁`. -/
theorem pauliY_lie_pauliZ : ⁅pauliY, pauliZ⁆ = (2 * I) • pauliX := sorry

/-- **`[Z, X] = 2iY`** (Nielsen & Chuang, Exercise 2.40, eq. 2.73), i.e. `⁅σ₃, σ₁⁆ = 2i σ₂`. -/
theorem pauliZ_lie_pauliX : ⁅pauliZ, pauliX⁆ = (2 * I) • pauliY := sorry

end AxQM.Concrete
