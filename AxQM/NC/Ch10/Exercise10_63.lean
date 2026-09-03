/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_52
import AxQM.Basic.API.PureState
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.ControlBranchExt
import AxQM.Basic.API.ThreeQubitBitFlipCode

/-!
# Nielsen & Chuang, Exercise 10.63 — a `Z̄ ↔ X̄` normalizer is the encoded Hadamard

*(N&C p. 482.)*

If U maps Steane code to itself with UZbarU-dag=Xbar, UXbarU-dag=Zbar, then U acts as encoded
Hadamard.

* `steaneLogical_overlap_eq_zero` — the codewords are orthogonal, `⟨0_L|1_L⟩ = 0`.
* `InSteaneCode` — "Maps the code into itself" is `InSteaneCode`, the predicate that a state's
  vector is a linear combination of the two codewords (they span the two-dimensional code).
* `steaneLogicalPlus` — the encoded `|+_L⟩ = (|0_L⟩ + |1_L⟩)/√2`.
* `steaneLogicalMinus` — the encoded `|−_L⟩ = (|0_L⟩ − |1_L⟩)/√2`.
* `steaneEncodedHadamard_action` — Exercise 10.63: any `U` mapping the code into itself with `U Z̄
  U† = X̄`, `U X̄ U† = Z̄` sends `|0_L⟩ ↦ (|0_L⟩+|1_L⟩)/√2` and `|1_L⟩ ↦ (|0_L⟩−|1_L⟩)/√2`, up to a
  *single* global phase (the two `toState` equalities plus the shared-phase `overlap` conjunct).
-/

namespace AxQM

open scoped InnerProductSpace

/-- **The Steane logical codewords are orthogonal**, `⟨0_L|1_L⟩ = 0`. -/
theorem steaneLogical_overlap_eq_zero :
    steaneLogicalZero.overlap steaneLogicalOne = 0 := by
  have h0 : steaneLogicalZBar.op steaneLogicalZero.vec = steaneLogicalZero.vec := by
    have h : steaneLogicalZBar.op steaneLogicalZero.vec = (1 : ℂ) • steaneLogicalZero.vec :=
      steaneLogicalZBar_hasEigenstate_logicalZero
    rwa [one_smul] at h
  have h1 : steaneLogicalZBar.op steaneLogicalOne.vec = -steaneLogicalOne.vec := by
    have h : steaneLogicalZBar.op steaneLogicalOne.vec = (-1 : ℂ) • steaneLogicalOne.vec :=
      steaneLogicalZBar_hasEigenstate_logicalOne
    rwa [neg_one_smul] at h
  have iso : inner ℂ (steaneLogicalZBar.op steaneLogicalZero.vec)
      (steaneLogicalZBar.op steaneLogicalOne.vec)
      = inner ℂ steaneLogicalZero.vec steaneLogicalOne.vec := by
    rw [← Evolution.toIsometryEquiv_apply, ← Evolution.toIsometryEquiv_apply,
      LinearIsometryEquiv.inner_map_map]
  rw [h0, h1, inner_neg_right] at iso
  rw [PureState.overlap_def]
  linear_combination (-(1 : ℂ) / 2) * iso

/-- **The Steane code space membership predicate.** A pure state `ψ` of the
seven-qubit register lies in the (two-dimensional) Steane code space iff its vector
is a linear combination `a|0_L⟩ + b|1_L⟩` of the two logical codewords, which span
the code. "`U` maps the Steane code into itself" is exactly
`InSteaneCode (U.evolvePure |0_L⟩) ∧ InSteaneCode (U.evolvePure |1_L⟩)`. -/
def InSteaneCode (ψ : PureState (bitReg (Fin 7))) : Prop :=
  ∃ a b : ℂ, ψ.vec = a • steaneLogicalZero.vec + b • steaneLogicalOne.vec

/-- **The encoded `|+_L⟩ = (|0_L⟩ + |1_L⟩)/√2`.** The normalized equal superposition
of the two Steane codewords. -/
noncomputable def steaneLogicalPlus : PureState (bitReg (Fin 7)) :=
  PureState.orthoPairOfOverlap steaneLogicalZero steaneLogicalOne steaneLogical_overlap_eq_zero
    ((Real.sqrt 2 : ℂ)⁻¹) ((Real.sqrt 2 : ℂ)⁻¹) (by rw [norm_sq_sqrtTwo_inv]; norm_num)

/-- **The encoded `|−_L⟩ = (|0_L⟩ − |1_L⟩)/√2`.** The normalized signed superposition
of the two Steane codewords. -/
noncomputable def steaneLogicalMinus : PureState (bitReg (Fin 7)) :=
  PureState.orthoPairOfOverlap steaneLogicalZero steaneLogicalOne steaneLogical_overlap_eq_zero
    ((Real.sqrt 2 : ℂ)⁻¹) (-(Real.sqrt 2 : ℂ)⁻¹) (by rw [norm_neg, norm_sq_sqrtTwo_inv]; norm_num)

/-- **Nielsen & Chuang, Exercise 10.63.** Any unitary `U` that maps the Steane code
into itself and conjugates `Z̄ ↦ X̄`, `X̄ ↦ Z̄` acts on the encoded basis as the
encoded Hadamard, up to a **single** global phase: `|0_L⟩ ↦ (|0_L⟩+|1_L⟩)/√2` and
`|1_L⟩ ↦ (|0_L⟩−|1_L⟩)/√2`.

The two `toState` (density-operator) equalities render "→ up to a global phase" for
each codeword; on their own they would allow *independent* phases on the two
codewords. The third conjunct, the equality of the overlaps
`⟪U|0_L⟩, |+_L⟩⟫ = ⟪U|1_L⟩, |−_L⟩⟫`, pins the two phases together, so `U` acts as the
encoded Hadamard up to one shared phase. -/
theorem steaneEncodedHadamard_action (U : Evolution (bitReg (Fin 7)))
    (hZX : U.comp (steaneLogicalZBar.comp U.adjoint) = steaneLogicalXBar)
    (hXZ : U.comp (steaneLogicalXBar.comp U.adjoint) = steaneLogicalZBar)
    (hmap : InSteaneCode (U.evolvePure steaneLogicalZero) ∧
            InSteaneCode (U.evolvePure steaneLogicalOne)) :
    (U.evolvePure steaneLogicalZero).toState = steaneLogicalPlus.toState ∧
    (U.evolvePure steaneLogicalOne).toState = steaneLogicalMinus.toState ∧
    (U.evolvePure steaneLogicalZero).overlap steaneLogicalPlus
      = (U.evolvePure steaneLogicalOne).overlap steaneLogicalMinus := sorry

end AxQM
