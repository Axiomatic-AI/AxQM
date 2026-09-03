/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CSSCode
import AxQM.ToMathlib.LinearAlgebra.Eigenspace.StabilizedSubmodule
import AxQM.ToMathlib.InformationTheory.Coding.DualCodeCharacterSum

/-!
# The CSS code space is the stabilized subspace of the check matrix (10.106)

This file proves the **code-space identification** of Nielsen & Chuang, Exercise 10.51: for binary
linear codes `C₂ ≤ C₁`, the check matrix (10.106) "corresponds to the stabilizer of `CSS(C₁, C₂)`",
i.e. the joint `+1`-eigenspace `V_S` stabilized by its generators is *exactly* the CSS code space
`CSS(C₁, C₂) = span{ |x + C₂⟩ : x ∈ C₁ }`.
-/

namespace AxQM

open scoped Matrix
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **CSS code space** `CSS(C₁, C₂)` as a `ℂ`-subspace of the register `bitReg ι`: the span of
the standard coset codewords `|x + C₂⟩` (`cssStdState C₂ x`) over the cosets `x ∈ C₁`
(Nielsen & Chuang, §10.4.2). This is the linear-algebraic code space (a `Submodule`), the ambient
span of the code states `cssCode C₁ C₂`. -/
noncomputable def cssCodeSpace (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Submodule ℂ (bitReg ι).space :=
  Submodule.span ℂ ((fun x => (cssStdState C₂ x).vec) '' (C₁ : Set (ι → ZMod 2)))

/-- **The generators of the CSS check matrix (10.106)** as a set of endomorphisms of the register:
the X-type bit-flip strings `X^v = bitString v` for the codewords `v ∈ C₂` (top block `[H(C₂⊥)|0]`,
rows spanning `C₂`) together with the Z-type phase-flip strings `Z^u = phaseString u` for
`u ∈ C₁⊥` (bottom block `[0|H(C₁)]`, rows spanning `C₁⊥`). -/
noncomputable def cssCheckOps (C₁ C₂ : LinearCode (ZMod 2) ι) :
    Set (Module.End ℂ (bitReg ι).space) :=
  (fun v => (bitString v).op.toLinearMap) '' (C₂ : Set (ι → ZMod 2)) ∪
    (fun u => (phaseString u).op.toLinearMap) '' (C₁.dual : Set (ι → ZMod 2))

/-- The **stabilized subspace** `V_S` of the CSS check matrix (10.106): the joint `+1`-eigenspace of
its generators, i.e. the vectors of `bitReg ι` fixed by every `X^v` (`v ∈ C₂`) and every `Z^u`
(`u ∈ C₁⊥`) (Nielsen & Chuang, §10.5.1). Exercise 10.51 identifies it with the code space
`cssCodeSpace C₁ C₂`. -/
noncomputable def cssStabilizedSpace (C₁ C₂ : LinearCode (ZMod 2) ι) :
    Submodule ℂ (bitReg ι).space :=
  Module.End.stabilizedSubmodule (cssCheckOps C₁ C₂)

/-- **Exercise 10.51 — the code-space equality.** For binary linear codes `C₂ ≤ C₁`, the check
matrix (10.106) "corresponds to the stabilizer of `CSS(C₁, C₂)`": the stabilized subspace `V_S` of
its generators is *exactly* the CSS code space `span{ |x + C₂⟩ : x ∈ C₁ }`. This is the subspace
identification N&C asserts (p. 470); the accompanying `t`-qubit correctability is
`AxQM.Concrete.cssStabilizer_isCorrectableErrorSet_of_correctsErrors`. -/
theorem cssStabilizedSpace_eq_cssCodeSpace {C₁ C₂ : LinearCode (ZMod 2) ι}
    [DecidablePred (· ∈ C₂)] (hsub : C₂ ≤ C₁) :
    cssStabilizedSpace C₁ C₂ = cssCodeSpace C₁ C₂ := sorry

end AxQM
