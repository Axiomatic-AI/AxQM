/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelEmbedding
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card

/-!
# Concrete: the controlled single-qubit gate (N&C §4.5.2, the controlled-`Ũ` step)

(Nielsen & Chuang §4.5.2, p. 191–193.)
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- The two active states `c[j↦0]` and `c[j↦1]` differ (at bit `j`), hence are distinct. -/
theorem update_zero_ne_update_one {j : Fin m} (c : Fin m → Fin 2) :
    Function.update c j 0 ≠ Function.update c j 1 := by
  intro h
  have := congrFun h j
  simp only [Function.update_self] at this
  exact absurd this (by decide)

/-- **A fibrewise gate on wire `j`.** For an encoding `enc : (Fin m → Fin 2) ≃ Fin d`, a wire `j`,
and a family `f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ` of `2 × 2` blocks indexed by the
off-`j` bit-pattern, `wireGate enc j f` is the `d × d` matrix that, on the basis state `|enc x⟩`,
acts on the `j`-th bit's two-dimensional fibre by the block `f x` (read at the pattern with bit `j`
normalised to `0`), fixing the other bits. -/
def wireGate (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i i' =>
    if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then
      f (Function.update (enc.symm i) j 0) (enc.symm i j) (enc.symm i' j)
    else 0

/-- Unfolding lemma for `wireGate` entries. -/
theorem wireGate_apply (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) (i i' : Fin d) :
    wireGate enc j f i i' =
      if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then
        f (Function.update (enc.symm i) j 0) (enc.symm i j) (enc.symm i' j)
      else 0 := rfl

/-- **The action of a fibrewise gate on a vector.** It mixes only the two components whose
bit-strings agree off wire `j`, through the block `f` (read at the fibre representative). -/
theorem wireGate_mulVec (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d) :
    (wireGate enc j f *ᵥ v) i =
      f (Function.update (enc.symm i) j 0) (enc.symm i j) 0
          * v (enc (Function.update (enc.symm i) j 0))
        + f (Function.update (enc.symm i) j 0) (enc.symm i j) 1
          * v (enc (Function.update (enc.symm i) j 1)) := by
  classical
  simp only [Matrix.mulVec, dotProduct, wireGate, Matrix.of_apply]
  set X := enc.symm i with hX
  set p := enc (Function.update X j 0) with hp
  set q := enc (Function.update X j 1) with hq
  have hpq : p ≠ q := enc.injective.ne (update_zero_ne_update_one X)
  have hp' : enc.symm p = Function.update X j 0 := by rw [hp, Equiv.symm_apply_apply]
  have hq' : enc.symm q = Function.update X j 1 := by rw [hq, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_add p q hpq (fun c _ hc => ?_) (by simp) (by simp)]
  · -- the two surviving terms `p`, `q`
    have hcondp : ∀ k, k ≠ j → X k = enc.symm p k := by
      intro k hk; rw [hp', Function.update_of_ne hk]
    have hcondq : ∀ k, k ≠ j → X k = enc.symm q k := by
      intro k hk; rw [hq', Function.update_of_ne hk]
    rw [if_pos hcondp, if_pos hcondq, hp', hq', Function.update_self, Function.update_self]
  · -- every other index contributes `0`
    have hcond : ¬ ∀ k, k ≠ j → X k = enc.symm c k := by
      intro hcond
      have hupd : enc.symm c = Function.update X j (enc.symm c j) := by
        funext k
        rcases eq_or_ne k j with rfl | hk
        · rw [Function.update_self]
        · rw [Function.update_of_ne hk, ← hcond k hk]
      rcases (show enc.symm c j = 0 ∨ enc.symm c j = 1 from by omega) with h0 | h1
      · exact hc.1 (by rw [← Equiv.symm_apply_eq, hupd, h0])
      · exact hc.2 (by rw [← Equiv.symm_apply_eq, hupd, h1])
    rw [if_neg hcond, zero_mul]

/-- **Fibrewise gates multiply blockwise**:
`wireGate enc j f * wireGate enc j g = wireGate enc j (fun y => f y * g y)`. -/
theorem wireGate_mul (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f g : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    wireGate enc j f * wireGate enc j g = wireGate enc j (fun y => f y * g y) := by
  have key : ∀ (v : Fin d → ℂ) (i : Fin d),
      ((wireGate enc j f * wireGate enc j g) *ᵥ v) i
        = (wireGate enc j (fun y => f y * g y) *ᵥ v) i := by
    intro v i
    rw [← Matrix.mulVec_mulVec]
    simp only [wireGate_mulVec, Equiv.symm_apply_apply, Function.update_self,
      Function.update_idem, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  ext i i'
  have h1 := key (fun x => if x = i' then (1 : ℂ) else 0) i
  simpa only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h1

/-- **The fibrewise gate with the constant identity block is the identity.** -/
theorem wireGate_one (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) :
    wireGate enc j (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i i'
  simp only [wireGate_apply, Matrix.one_apply]
  by_cases h : i = i'
  · subst h; simp
  · rw [if_neg h]
    by_cases hoff : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
    · rw [if_pos hoff, if_neg]
      intro hj
      exact h (enc.symm.injective (funext fun k => by
        rcases eq_or_ne k j with rfl | hk
        · exact hj
        · exact hoff k hk))
    · rw [if_neg hoff]

/-- **A fibrewise gate commutes with the conjugate transpose**: `(wireGate enc j f)ᴴ = wireGate enc
j (fun y => (f y)ᴴ)`. -/
theorem wireGate_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    (wireGate enc j f)ᴴ = wireGate enc j (fun y => (f y)ᴴ) := by
  ext i i'
  rw [Matrix.conjTranspose_apply, wireGate_apply, wireGate_apply]
  by_cases hoff : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
  · rw [if_pos hoff, if_pos (fun k hk => (hoff k hk).symm)]
    have hrep : Function.update (enc.symm i') j 0 = Function.update (enc.symm i) j 0 := by
      funext k
      rcases eq_or_ne k j with rfl | hk
      · rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, hoff k hk]
    rw [hrep, Matrix.conjTranspose_apply]
  · rw [if_neg hoff, if_neg (fun h => hoff (fun k hk => (h k hk).symm)), star_zero]

end AxQM.Concrete
