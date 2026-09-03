/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-! # The minimal operator-sum representation: at most `d²` operation elements

For a finite family of operation elements `E : ι → (H →L[ℂ] G)`, the **operator-sum map**
`ContinuousLinearMap.krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` may be indexed by an arbitrarily large `ι`.
This file proves that it can always be re-expressed with at most `dim G · dim H` operation
elements — and, in the square case `G = H`, at most `d²` where `d = dim H`. This is
Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Theorem 8.3** (the square
case, `exists_krausSumₗ_eq_fin_finrank_sq`), together with its `d`-to-`d′` generalization,
**Exercise 8.11** (`exists_krausSumₗ_eq_fin_finrank`).

## Main results

* `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank` — **Exercise 8.11**: every operator-sum
  map on a `d`-input, `d′`-output space has an equal operator-sum map indexed by
  `Fin (dim G · dim H)`.
* `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank_sq` — **Theorem 8.3**: on a `d`-dimensional
  system (`G = H`), an equal operator-sum map indexed by `Fin (d²)`.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **Minimal operator-sum representation, `d`-to-`d′` form** (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 8.11). -/
theorem exists_krausSumₗ_eq_fin_finrank {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G) :
    ∃ F : Fin (Module.finrank ℂ G * Module.finrank ℂ H) → (H →L[ℂ] G),
      krausSumₗ F = krausSumₗ E := sorry

/-- **Minimal operator-sum representation on a `d`-dimensional system** (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Theorem 8.3). -/
theorem exists_krausSumₗ_eq_fin_finrank_sq {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] H) :
    ∃ F : Fin (Module.finrank ℂ H ^ 2) → (H →L[ℂ] H), krausSumₗ F = krausSumₗ E := sorry

end ContinuousLinearMap
