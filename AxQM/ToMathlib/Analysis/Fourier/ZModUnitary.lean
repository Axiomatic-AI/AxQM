/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Unitarity of the discrete / quantum Fourier transform matrix

This file defines the symmetrically normalized discrete Fourier transform matrix on `ZMod N`
— the matrix underlying the *quantum Fourier transform* — and states that it is unitary.

## Main definitions

* `ZMod.dftMatrix N` : the `N × N` complex matrix with entries `(dftMatrix N) j k = N⁻¹ᐟ² · exp
  (2πijk / N)`, indexed by `ZMod N`. This is exactly the linear operator whose action on basis
  states is `|j⟩ ↦ N⁻¹ᐟ² ∑ₖ exp(2πijk/N) |k⟩`.

## Main statements

* `ZMod.dftMatrix_mem_unitaryGroup` : `dftMatrix N` is unitary, i.e. it lies in
  `Matrix.unitaryGroup (ZMod N) ℂ`.
-/

@[expose] public section

open scoped BigOperators

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The symmetrically normalized discrete Fourier transform matrix on `ZMod N`, i.e. the
**quantum Fourier transform** matrix.  Its `(j, k)` entry is `N⁻¹ᐟ² · stdAddChar (j · k)`, and
since `stdAddChar (j · k) = exp (2πijk / N)` this is `N⁻¹ᐟ² · exp (2πijk / N)`, matching the
Nielsen & Chuang definition `|j⟩ ↦ N⁻¹ᐟ² ∑ₖ exp(2πijk/N) |k⟩`. -/
noncomputable def dftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun j k => (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (j * k)

/-- **The quantum Fourier transform is unitary** (Nielsen & Chuang, Exercise 5.1): the DFT matrix
`dftMatrix N` lies in the unitary group. -/
theorem dftMatrix_mem_unitaryGroup (N : ℕ) [NeZero N] :
    dftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := sorry

end ZMod
