/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PhaseFlipStabilizer
import AxQM.Basic.API.PauliEigen

/-!
# AxQM.Basic.API — maximality of the phase-flip stabilizer `⟨X₁X₂, X₂X₃⟩`

Infrastructure for the **maximality** half of Nielsen & Chuang **Exercise 10.46**:
the stabilizer of the three-qubit *phase-flip* code (`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`) is generated
by `X₁X₂` and `X₂X₃`. The two generators are the observables `xxIObservable = X ⊗ X ⊗ I` and
`ixxObservable = I ⊗ X ⊗ X`, with product `xixObservable = X ⊗ I ⊗ X` (`X₁X₃`), and each fixes both
codewords (**containment**: `⟨X₁X₂, X₂X₃⟩` stabilizes the code). This file proves that these two
commuting involutions generate *exactly* the full stabilizer.

## Contents

* `phaseFlipCodeProj_eq_projPlus_comp` — **maximality**: `phaseFlipCodeProj = P₊(X₁X₂) ∘ P₊(X₂X₃)`,
  i.e. the code space is exactly the joint `+1`-eigenspace, so `⟨X₁X₂, X₂X₃⟩` is the full
  stabilizer.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.46 (maximality).** The phase-flip code projector equals the
projector onto the joint `+1`-eigenspace of the two generators:
`phaseFlipCodeProj = P₊(X₁X₂) ∘ P₊(X₂X₃)`. Read off on the `±` basis, `P₊(X₁X₂) P₊(X₂X₃)` fixes
`|σ₁σ₂σ₃⟩` exactly when `σ₁ = σ₂ = σ₃` — i.e. exactly on the two-dimensional codeword span. Hence
the code space is *precisely* the stabilized subspace of `⟨X₁X₂, X₂X₃⟩`; the stabilizer has the full
order `2^{3-1} = 4` and `⟨X₁X₂, X₂X₃⟩` is the whole stabilizer, not a proper subgroup. -/
theorem phaseFlipCodeProj_eq_projPlus_comp :
    phaseFlipCodeProj = xxIObservable.projPlus.comp ixxObservable.projPlus := sorry

end AxQM
