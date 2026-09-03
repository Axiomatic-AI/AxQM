/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic — quantum systems

A **quantum system** is the physical object whose mathematical realization is a
finite-dimensional complex Hilbert space.

## Main definitions

* `QSystem` — a quantum system: a bundled finite-dimensional complex Hilbert space.
* `QSystem.compose` (`S ⊗ T`) — the composite system: systems compose by
  the tensor product of their state spaces.
-/

open scoped TensorProduct

namespace AxQM

/-- A **quantum system**: the physical object whose mathematical realization is a
finite-dimensional complex Hilbert space `space`. -/
structure QSystem where
  /-- The underlying Hilbert space. -/
  space : Type*
  [norm : NormedAddCommGroup space]
  [inner : InnerProductSpace ℂ space]
  [findim : FiniteDimensional ℂ space]

attribute [instance] QSystem.norm QSystem.inner QSystem.findim

/-- A system **coerces to its state space**: `↑S` is `S.space`, so `S : QSystem` stands in wherever
a type/vector/operator is expected (`x : S`, `op : S →L[ℂ] S`). -/
instance : CoeSort QSystem (Type _) := ⟨QSystem.space⟩

/-- The **dimension** of a quantum system: the (finite) dimension `finrank ℂ S.space` of its state
space. -/
noncomputable def QSystem.dim (S : QSystem) : ℕ := Module.finrank ℂ S.space

/-- **Composite system** (N&C §2.2.8): two systems
compose to a system whose state space is the tensor product of the components'. The
physical content is the *choice* of the tensor product (over, say, a direct sum). -/
noncomputable def QSystem.compose (S T : QSystem) : QSystem :=
  { space := S.space ⊗[ℂ] T.space }

@[inherit_doc] scoped infixr:70 " ⊗ " => QSystem.compose

/-- **A quantum system from a model Hilbert space**: wrap a finite-dimensional complex Hilbert space
`H` as the system whose state space is `H`. -/
def QSystem.ofModel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] : QSystem := { space := H }

end AxQM
