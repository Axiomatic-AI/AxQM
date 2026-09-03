/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel

/-!
# Concrete: embedding a 2×2 unitary into a coordinate pair of a `d × d` matrix (N&C §4.5.1)

The two-level decomposition of an arbitrary `d × d` unitary (Nielsen & Chuang §4.5.1, p. 189) is
built from *two-level* unitaries, each of which is a single `2 × 2` unitary block placed into a
chosen coordinate pair `{p, q}` and acting as the identity everywhere else. This file provides that
general **embedding** primitive `twoLevelEmbed p q G`, independently of the particular `2 × 2`
block chosen.

## The construction and its algebra

* `twoLevelEmbed_one` — it sends `1 ↦ 1`;
* `twoLevelEmbed_mul` — it is multiplicative, `embed A * embed B = embed (A * B)`;
* `twoLevelEmbed_conjTranspose` — it commutes with `ᴴ`, `(embed G)ᴴ = embed Gᴴ`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The two-level embedding.** `twoLevelEmbed p q G` places the `2 × 2` matrix `G` into the
`{p, q} × {p, q}` block of a `d × d` matrix (`p ↦ 0`, `q ↦ 1`) and is the identity on all other
entries. -/
def twoLevelEmbed (p q : Fin d) (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j =>
    if i = p then (if j = p then G 0 0 else if j = q then G 0 1 else 0)
    else if i = q then (if j = p then G 1 0 else if j = q then G 1 1 else 0)
    else if i = j then 1 else 0

/-- Unfolding lemma for `twoLevelEmbed` entries. -/
theorem twoLevelEmbed_apply (p q : Fin d) (G : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin d) :
    twoLevelEmbed p q G i j =
      if i = p then (if j = p then G 0 0 else if j = q then G 0 1 else 0)
      else if i = q then (if j = p then G 1 0 else if j = q then G 1 1 else 0)
      else if i = j then 1 else 0 := rfl

variable {p q : Fin d} {G A B : Matrix (Fin 2) (Fin 2) ℂ}

/-- The embedding of the `2 × 2` identity is the `d × d` identity. -/
theorem twoLevelEmbed_one (h : p ≠ q) :
    twoLevelEmbed p q (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  rw [twoLevelEmbed_apply]
  simp only [Matrix.one_apply]
  split_ifs <;> simp_all

/-- **`twoLevelEmbed p q` is multiplicative on the block** (`p ≠ q`): embedding respects matrix
products. -/
theorem twoLevelEmbed_mul (h : p ≠ q) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevelEmbed p q A * twoLevelEmbed p q B = twoLevelEmbed p q (A * B) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hip : i = p
  · rw [Finset.sum_eq_add p q h
      (fun c _ hc => by simp [twoLevelEmbed_apply, hip, hc.1, hc.2]) (by simp) (by simp)]
    by_cases hjp : j = p <;> by_cases hjq : j = q <;>
      simp [twoLevelEmbed_apply, hip, hjp, hjq, Ne.symm h, Matrix.mul_apply,
        Fin.sum_univ_two]
  · by_cases hiq : i = q
    · rw [Finset.sum_eq_add p q h
        (fun c _ hc => by simp [twoLevelEmbed_apply, hiq, hc.1, hc.2]) (by simp) (by simp)]
      by_cases hjp : j = p <;> by_cases hjq : j = q <;>
        simp [twoLevelEmbed_apply, hiq, hjp, hjq, Ne.symm h, Matrix.mul_apply,
          Fin.sum_univ_two]
    · rw [Finset.sum_eq_single i
        (fun c _ hc => by simp [twoLevelEmbed_apply, hip, hiq, Ne.symm hc]) (by simp)]
      simp [twoLevelEmbed_apply, hip, hiq]

/-- **`twoLevelEmbed p q` commutes with the conjugate transpose**:
`(embed G)ᴴ = embed Gᴴ`. -/
theorem twoLevelEmbed_conjTranspose (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoLevelEmbed p q G)ᴴ = twoLevelEmbed p q Gᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, twoLevelEmbed_apply, twoLevelEmbed_apply]
  simp only [Matrix.conjTranspose_apply]
  split_ifs <;> simp <;> simp_all

/-- **An embedded `2 × 2` unitary is a two-level unitary** (`p ≠ q`), with `{p, q}` its
distinguished block. -/
theorem isTwoLevelUnitary_twoLevelEmbed (h : p ≠ q)
    (hG : G ∈ Matrix.unitaryGroup (Fin 2) ℂ) : IsTwoLevelUnitary (twoLevelEmbed p q G) := by
  refine ⟨?_, p, q, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff'] at hG ⊢
    rw [Matrix.star_eq_conjTranspose] at hG ⊢
    rw [twoLevelEmbed_conjTranspose, twoLevelEmbed_mul h, hG, twoLevelEmbed_one h]
  · intro i j hij
    rw [twoLevelEmbed_apply, Matrix.one_apply]
    rcases hij with ⟨hip, hiq⟩ | ⟨hjp, hjq⟩ <;> split_ifs <;> simp_all

end AxQM.Concrete
