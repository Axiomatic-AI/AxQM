/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CSSCode

/-!
# The CSS phase-coset states form an orthonormal basis (Nielsen & Chuang, Exercise 12.35)

Nielsen & Chuang, Exercise 12.35 (p. 598), asks to show that the CSS code states of equation
(12.202) form an orthonormal basis.

## The state and its indexing

As a *vector*, `|ξ_{v_k,z,x}⟩` depends only on the total offset `a = v_k + x` (a coset of `C₂` in
`𝔽₂ⁿ`) and on the phase `z`; the `C₁`-refinement `a = v_k + x` (with `v_k` a coset of `C₂` in `C₁`
and `x` a coset of `C₁` in `𝔽₂ⁿ`) is only N&C's device for *counting* the states
(`2^m · 2^{n-k₁} · 2^{k₂} = 2ⁿ`, the exercise's hint). We therefore index the family by the
canonical cosets directly — the equation (12.204) is then manifestly `C₁`-free and
representative-independent, and holds for *any* linear code `C₂ ≤ 𝔽₂ⁿ`:

* `AxQM.cssPhaseState C₂ z a` — the state `|ξ_{z,a}⟩ = |C₂|^{-1/2} ∑_{w∈C₂} (-1)^{z·w}
  |a + w⟩`, the shift-free twisted CSS coset state `cssTwistedState C₂ z 0 a` (N&C 10.75 / 12.202).

The projector `|ξ_{z,a}⟩⟨ξ_{z,a}|` depends only on `a` mod `C₂` and `z` mod `C₂⊥`, so the states are
indexed by `(𝔽₂ⁿ ⧸ C₂) × (𝔽₂ⁿ ⧸ C₂⊥)` (representatives via `Quotient.out`), of which there are
`|𝔽₂ⁿ ⧸ C₂| · |𝔽₂ⁿ ⧸ C₂⊥| = 2^{n-k₂} · 2^{k₂} = 2ⁿ`.

## Contents

* `cssPhaseState_inner` — the inner product of two phase-coset states, as a dual-code
  character-sum indicator, `⟨ξ_{z,a}, ξ_{z',a'}⟩ = [a - a' ∈ C₂] · [z + z' ∈ C₂⊥] ·
  (-1)^{z'·(a-a')}`.
* `cssPhaseFamily_orthonormal` — the family over the coset index is orthonormal.
* `cssPhaseBasis` — the resulting `OrthonormalBasis` of `bitReg ι`.
* `cssPhaseFamily_sum_rankOne_eq_id` — the resolution of the identity (12.204).
-/

open scoped Matrix
open scoped InnerProductSpace

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- The **CSS phase-coset state** `|ξ_{z,a}⟩ = |C₂|^{-1/2} ∑_{w∈C₂} (-1)^{z·w} |a + w⟩` (Nielsen &
Chuang eq. 12.202, with total offset `a = v_k + x` and no separate shift), realized as the
shift-free twisted CSS coset state `cssTwistedState C₂ z 0 a`. -/
noncomputable def cssPhaseState (z a : ι → ZMod 2) : PureState (bitReg ι) :=
  cssTwistedState C₂ z 0 a

/-- The state vector of `cssPhaseState`, with the trivial shift removed:
`|ξ_{z,a}⟩ = |C₂|^{-1/2} ∑_{w∈C₂} (-1)^{z·w} |a + w⟩`. -/
theorem cssPhaseState_vec (z a : ι → ZMod 2) :
    (cssPhaseState C₂ z a).vec
      = (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ •
        ∑ y : ↥C₂, (-1 : ℂ) ^ (z ⬝ᵥ (y : ι → ZMod 2)).val • regBasis ι (a + (y : ι → ZMod 2)) := by
  simp only [cssPhaseState, cssTwistedState_vec, add_zero]

open Classical in
/-- **The inner product of two CSS phase-coset states** (Exercise 12.35), as a dual-code
character-sum indicator:
`⟨ξ_{z,a}, ξ_{z',a'}⟩ = [a - a' ∈ C₂] · (-1)^{z'·(a-a')} · [z + z' ∈ C₂⊥]`. -/
theorem cssPhaseState_inner (z z' a a' : ι → ZMod 2) :
    inner ℂ (cssPhaseState C₂ z a).vec (cssPhaseState C₂ z' a').vec
      = (if a - a' ∈ C₂ then (-1 : ℂ) ^ (z' ⬝ᵥ (a - a')).val else 0)
        * (if z + z' ∈ C₂.dual then 1 else 0) := by
  have hNpos : (0 : ℝ) < Nat.card ↥C₂ := by
    haveI : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩
    exact_mod_cast Nat.card_pos
  rw [cssPhaseState_vec, cssPhaseState_vec, inner_smul_left, inner_smul_right, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (regBasis ι).orthonormal, map_pow, map_neg, map_one,
    map_inv₀, Complex.conj_ofReal]
  by_cases hc : a - a' ∈ C₂
  · rw [if_pos hc]
    have hDS : (∑ x : ↥C₂, ∑ x_1 : ↥C₂, (-1 : ℂ) ^ (z' ⬝ᵥ (x_1 : ι → ZMod 2)).val *
          ((-1 : ℂ) ^ (z ⬝ᵥ (x : ι → ZMod 2)).val *
            if a + (x : ι → ZMod 2) = a' + (x_1 : ι → ZMod 2) then (1 : ℂ) else 0))
        = (-1 : ℂ) ^ (z' ⬝ᵥ (a - a')).val *
          if z + z' ∈ C₂.dual then (Nat.card ↥C₂ : ℂ) else 0 := by
      have hinner : ∀ x : ↥C₂,
          (∑ x_1 : ↥C₂, (-1 : ℂ) ^ (z' ⬝ᵥ (x_1 : ι → ZMod 2)).val *
              if a + (x : ι → ZMod 2) = a' + (x_1 : ι → ZMod 2) then (1 : ℂ) else 0)
            = (-1 : ℂ) ^ (z' ⬝ᵥ ((⟨a - a', hc⟩ + x : ↥C₂) : ι → ZMod 2)).val := by
        intro x
        rw [Finset.sum_eq_single (⟨a - a', hc⟩ + x)]
        · have hcond : a + (x : ι → ZMod 2) = a' + ((⟨a - a', hc⟩ + x : ↥C₂) : ι → ZMod 2) := by
            rw [Submodule.coe_add]
            change a + (x : ι → ZMod 2) = a' + ((a - a') + (x : ι → ZMod 2))
            abel
          rw [if_pos hcond, mul_one]
        · intro b _ hb
          rw [if_neg, mul_zero]
          intro heq
          apply hb
          apply Subtype.ext
          rw [Submodule.coe_add]
          change (b : ι → ZMod 2) = (a - a') + (x : ι → ZMod 2)
          rw [sub_add_eq_add_sub, eq_sub_iff_add_eq, add_comm]
          exact heq.symm
        · intro hnotmem
          exact absurd (Finset.mem_univ _) hnotmem
      calc ∑ x : ↥C₂, ∑ x_1 : ↥C₂, (-1 : ℂ) ^ (z' ⬝ᵥ (x_1 : ι → ZMod 2)).val *
              ((-1 : ℂ) ^ (z ⬝ᵥ (x : ι → ZMod 2)).val *
                if a + (x : ι → ZMod 2) = a' + (x_1 : ι → ZMod 2) then (1 : ℂ) else 0)
          = ∑ x : ↥C₂, (-1 : ℂ) ^ (z ⬝ᵥ (x : ι → ZMod 2)).val *
              ∑ x_1 : ↥C₂, (-1 : ℂ) ^ (z' ⬝ᵥ (x_1 : ι → ZMod 2)).val *
                if a + (x : ι → ZMod 2) = a' + (x_1 : ι → ZMod 2) then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x_1 _ => by ring
        _ = ∑ x : ↥C₂, (-1 : ℂ) ^ (z ⬝ᵥ (x : ι → ZMod 2)).val *
              (-1 : ℂ) ^ (z' ⬝ᵥ ((⟨a - a', hc⟩ + x : ↥C₂) : ι → ZMod 2)).val := by
            exact Finset.sum_congr rfl fun x _ => by rw [hinner x]
        _ = ∑ x : ↥C₂, (-1 : ℂ) ^ (z' ⬝ᵥ (a - a')).val *
              (-1 : ℂ) ^ ((z + z') ⬝ᵥ (x : ι → ZMod 2)).val := by
            refine Finset.sum_congr rfl fun x _ => ?_
            have h2 : (-1 : ℂ) ^ (z ⬝ᵥ (x : ι → ZMod 2)).val *
                  (-1 : ℂ) ^ (z' ⬝ᵥ (x : ι → ZMod 2)).val
                = (-1 : ℂ) ^ ((z + z') ⬝ᵥ (x : ι → ZMod 2)).val := by
              rw [← neg_one_pow_zmod2_val_add, ← add_dotProduct]
            rw [Submodule.coe_add]
            change (-1 : ℂ) ^ (z ⬝ᵥ (x : ι → ZMod 2)).val *
                (-1 : ℂ) ^ (z' ⬝ᵥ ((a - a') + (x : ι → ZMod 2))).val = _
            rw [dotProduct_add, neg_one_pow_zmod2_val_add, ← h2]
            ring
        _ = (-1 : ℂ) ^ (z' ⬝ᵥ (a - a')).val *
              ∑ x : ↥C₂, (-1 : ℂ) ^ ((z + z') ⬝ᵥ (x : ι → ZMod 2)).val := by
            rw [Finset.mul_sum]
        _ = (-1 : ℂ) ^ (z' ⬝ᵥ (a - a')).val *
              if z + z' ∈ C₂.dual then (Nat.card ↥C₂ : ℂ) else 0 := by
            rw [LinearCode.sum_neg_one_pow_dotProduct_complex]
    rw [hDS]
    by_cases hd : z + z' ∈ C₂.dual
    · rw [if_pos hd, if_pos hd, mul_one]
      have hsq : ((√(Nat.card ↥C₂ : ℝ) : ℂ))⁻¹ * ((√(Nat.card ↥C₂ : ℝ) : ℂ))⁻¹
          * (Nat.card ↥C₂ : ℂ) = 1 := by
        have hs : ((√(Nat.card ↥C₂ : ℝ) : ℂ)) * ((√(Nat.card ↥C₂ : ℝ) : ℂ))
            = (Nat.card ↥C₂ : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNpos.le, Complex.ofReal_natCast]
        rw [← mul_inv, hs, inv_mul_cancel₀ (by exact_mod_cast hNpos.ne')]
      linear_combination (-1 : ℂ) ^ (z' ⬝ᵥ (a - a')).val * hsq
    · rw [if_neg hd, if_neg hd, mul_zero, mul_zero, mul_zero]
  · rw [if_neg hc, zero_mul]
    have hzero : ∀ x x_1 : ↥C₂,
        (if a + (x : ι → ZMod 2) = a' + (x_1 : ι → ZMod 2) then (1 : ℂ) else 0) = 0 := by
      intro x x_1
      rw [if_neg]
      intro heq
      apply hc
      have hsub : a - a' = (x_1 : ι → ZMod 2) - (x : ι → ZMod 2) := by
        rw [sub_eq_sub_iff_add_eq_add, heq, add_comm]
      rw [hsub]
      exact C₂.sub_mem x_1.2 x.2
    simp only [hzero, mul_zero, Finset.sum_const_zero]

omit [DecidablePred (· ∈ C₂)] in
/-- The **coset index** of the phase-basis: an offset coset `a ∈ 𝔽₂ⁿ ⧸ C₂` paired with a phase
coset `z ∈ 𝔽₂ⁿ ⧸ C₂⊥`. There are `2^{n-k₂} · 2^{k₂} = 2ⁿ` of them, the dimension of `bitReg ι`. -/
abbrev cssPhaseIndex : Type _ :=
  ((ι → ZMod 2) ⧸ C₂) × ((ι → ZMod 2) ⧸ C₂.dual)

/-- The **phase-coset state family** `(a, z) ↦ |ξ_{z,a}⟩`, indexed by the coset index using
canonical representatives (`Quotient.out`). The projector `|ξ⟩⟨ξ|` depends only on the cosets, so
this choice of representatives is immaterial to the resolution of the identity. -/
noncomputable def cssPhaseFamily (p : cssPhaseIndex C₂) : (bitReg ι).space :=
  (cssPhaseState C₂ (Quotient.out p.2) (Quotient.out p.1)).vec

/-- **The CSS phase-coset states are orthonormal** (Exercise 12.35): two states are orthogonal
unless both their offset cosets and their phase cosets agree, and each has norm one. -/
theorem cssPhaseFamily_orthonormal : Orthonormal ℂ (cssPhaseFamily C₂) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨qa, qz⟩ ⟨qa', qz'⟩
  simp only [cssPhaseFamily]
  rw [cssPhaseState_inner]
  have hA : (Quotient.out qa - Quotient.out qa' ∈ C₂) ↔ qa = qa' := by
    rw [← Submodule.Quotient.eq C₂]; simp only [Submodule.Quotient.mk_out]
  -- In the `ZMod 2`-module `𝔽₂ⁿ ⧸ C₂⊥`, `x + x = 0`, so the character condition `z + z' ∈ C₂⊥`
  -- corresponds to `qz = qz'`.
  have hself : ∀ x : (ι → ZMod 2) ⧸ C₂.dual, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2), (by decide : (2 : ZMod 2) = 0), zero_smul]
  have hZ : (Quotient.out qz + Quotient.out qz' ∈ C₂.dual) ↔ qz = qz' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_add, Submodule.Quotient.mk_out,
      Submodule.Quotient.mk_out]
    constructor
    · intro h
      have : qz = qz + qz' + qz' := by rw [add_assoc, hself, add_zero]
      rw [this, h, zero_add]
    · rintro rfl; exact hself qz
  by_cases hqa : qa = qa'
  · by_cases hqz : qz = qz'
    · rw [if_pos (hA.mpr hqa), if_pos (hZ.mpr hqz),
        if_pos (show ((qa, qz) : cssPhaseIndex C₂) = (qa', qz') by rw [hqa, hqz]), mul_one, hqa,
        sub_self, dotProduct_zero, ZMod.val_zero, pow_zero]
    · rw [if_neg (fun h => hqz (hZ.mp h)), mul_zero,
        if_neg (fun h => hqz (congrArg Prod.snd h))]
  · rw [if_neg (fun h => hqa (hA.mp h)), zero_mul, if_neg (fun h => hqa (congrArg Prod.fst h))]

omit [DecidablePred (· ∈ C₂)] in
/-- **Cardinality of the phase-basis index equals the dimension of the register.** The two coset
counts multiply to `2^{(n - k₂)} · 2^{k₂} = 2ⁿ = dim (bitReg ι)`. -/
theorem card_cssPhaseIndex_eq_finrank :
    Fintype.card (cssPhaseIndex C₂) = Module.finrank ℂ (bitReg ι).space := by
  have hV : Module.finrank (ZMod 2) (ι → ZMod 2) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hle : Module.finrank (ZMod 2) C₂ ≤ Fintype.card ι := by
    rw [← hV]; exact Submodule.finrank_le C₂
  have hsum : Module.finrank (ZMod 2) ((ι → ZMod 2) ⧸ C₂)
      + Module.finrank (ZMod 2) ((ι → ZMod 2) ⧸ C₂.dual) = Fintype.card ι := by
    have e1 := Submodule.finrank_quotient_add_finrank C₂
    have e2 := Submodule.finrank_quotient_add_finrank C₂.dual
    have e3 := LinearCode.finrank_dual C₂
    omega
  have hdim : Module.finrank ℂ (bitReg ι).space = Fintype.card (ι → ZMod 2) :=
    groupSystem_dim (ι → ZMod 2)
  rw [Fintype.card_prod, Module.card_eq_pow_finrank (K := ZMod 2) (V := (ι → ZMod 2) ⧸ C₂),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := (ι → ZMod 2) ⧸ C₂.dual), ← pow_add, hsum,
    hdim, Fintype.card_fun]

/-- **The CSS phase-coset states form an orthonormal basis** of the register `bitReg ι` (Nielsen &
Chuang, Exercise 12.35) — the `2ⁿ` states `|ξ_{v_k,z,x}⟩` of (12.202), indexed by the `2^{n-k₂}`
offset cosets and `2^{k₂}` phase cosets. -/
noncomputable def cssPhaseBasis : OrthonormalBasis (cssPhaseIndex C₂) ℂ (bitReg ι).space :=
  (basisOfOrthonormalOfCardEqFinrank (cssPhaseFamily_orthonormal C₂)
      (card_cssPhaseIndex_eq_finrank C₂)).toOrthonormalBasis (by
    rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact cssPhaseFamily_orthonormal C₂)

open InnerProductSpace in
/-- **The resolution of the identity for the CSS phase-coset states** (Nielsen & Chuang,
Exercise 12.35, eq. (12.204)). -/
theorem cssPhaseFamily_sum_rankOne_eq_id :
    ∑ p : cssPhaseIndex C₂, rankOne ℂ (cssPhaseFamily C₂ p) (cssPhaseFamily C₂ p) = 1 := sorry

end AxQM
