/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.Qudit
import AxQM.Basic.Composite
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the two-register computational-basis permutation gate

The operator-level form of a *classical reversible circuit* on a pair of qudit registers: given a
permutation `σ` of the joint computational-basis labels `Fin d × Fin e`, the corresponding gate
is the unitary `Evolution` of `qudit d ⊗ qudit e` sending each basis state `|x⟩ ⊗ |y⟩` to
`|(σ (x, y)).1⟩ ⊗ |(σ (x, y)).2⟩`. Every permutation of the basis is realised by such a unitary
(permuting an orthonormal basis is an isometry), so this is the general "permute the computational
basis" gate — the operator a reversible classical circuit on the two registers implements.

## Main declarations
* `quditPairBasis d e` — the computational **product** orthonormal basis of
  `(qudit d ⊗ qudit e).space`, indexed by `Fin d × Fin e`: `Mathlib`'s
  `OrthonormalBasis.tensorProduct` of the two standard bases:
  `quditPairBasis d e (x, y) = |x⟩ ⊗ |y⟩`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {d e : ℕ}

/-- The **computational product basis** of `(qudit d ⊗ qudit e).space`, indexed by `Fin d × Fin e`:
the `Mathlib` tensor product `OrthonormalBasis.tensorProduct` of the two standard bases
`EuclideanSpace.basisFun`. -/
def quditPairBasis (d e : ℕ) :
    OrthonormalBasis (Fin d × Fin e) ℂ (qudit d ⊗ qudit e).space :=
  (EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct (EuclideanSpace.basisFun (Fin e) ℂ)

end AxQM
