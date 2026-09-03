/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
import AxQM.Basic.QSystem
import AxQM.Basic.SystemIso

/-!
# AxQM.Basic — indexed composite systems (`⨂ₛ i, S i`)

Systems *compose* by the tensor product of their state spaces.
`QSystem.compose` (`S ⊗ T`) is the binary form. This file introduces the
**indexed** form `QSystem.piTensor` (`⨂ₛ i, S i`), the composite of a whole finite family of
systems over the n-ary `PiTensorProduct`.

## Main definitions

* `QSystem.piTensor` (`⨂ₛ i, S i`) — the indexed composite system of a finite family
  `S : ι → QSystem`: the system whose state space is the n-ary tensor product `⨂[ℂ] i, (S i).space`.
-/

open scoped TensorProduct

namespace AxQM

/-- **Indexed composite system** (n-ary form): a finite family of systems
`S : ι → QSystem` composes to a system whose state space is the n-ary tensor product
`⨂[ℂ] i, (S i).space`. The design-primary composite — the binary `S ⊗ T` is the two-factor
case. The physical content is the *choice* of the tensor product; the mathematics (including
finite-dimensionality, via the tensor-product basis) is delegated to the bulk. -/
noncomputable def QSystem.piTensor {ι : Type*} [Fintype ι] (S : ι → QSystem) : QSystem where
  space := ⨂[ℂ] i, (S i).space
  findim := Module.Basis.finiteDimensional_of_finite
    (Basis.piTensorProduct fun i ↦ Module.finBasis ℂ (S i).space)

@[inherit_doc QSystem.piTensor]
scoped notation3:100 "⨂ₛ "(...)", "r:67:(scoped f => QSystem.piTensor f) => r

/-- **`n`-fold tensor power** of a system: `S ^⊗ₛ n = ⨂ₛ (_ : Fin n), S`, the composite of
`n` copies of `S`. The constant-family case of the indexed
composite `⨂ₛ` — `n` registers of the same system, the shape the register/many-body
constructions read off directly. -/
noncomputable def QSystem.tensorPow (S : QSystem) (n : ℕ) : QSystem := ⨂ₛ _ : Fin n, S

-- The subscript `ₛ` (system) is deliberate: bare `^⊗` is already a global Mathlib notation. As a
-- `scoped` 3-glyph token, `^⊗ₛ` wins longest-match over `^⊗` wherever `AxQM` is
-- open/scoped (every intended use site); outside that scope it would fall back to `^⊗`.
@[inherit_doc QSystem.tensorPow] scoped infixr:75 " ^⊗ₛ " => QSystem.tensorPow

end AxQM
