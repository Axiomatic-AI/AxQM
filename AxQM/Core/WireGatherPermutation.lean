/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.PlacedMultiControlledX

/-!
# Realising a *chosen* `Cᵏ(X)` gate `(S, t)` (N&C Exercise 4.29, evolution-realization brick 11)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The recursive Barenco construction bottoms out
into a sequence of multiply-controlled `NOT` gates `Cᵏ(X)` (`k ≤ 2` are exactly the
`Toffoli`/`CNOT`/`NOT` gates), **each addressed to a prescribed control set `S` and target wire
`t`** of the register — the gate `Concrete.mcNot S t` of the classical circuit
`Concrete.mcNotDenote`.

## Main declarations
* `wireGatherPerm S t hk ht` — the **wire-gather permutation** of `Fin (k + 1 + b)`: for a control
  set `S` with `S.card = k` and a target `t ∉ S`, an `Equiv.Perm` that sends the `k` front control
  wires (`Fin.castAdd b ∘ Fin.castSucc`) onto `S` (in increasing order), the front target wire
  (`Fin.castAdd b (Fin.last k)`) onto `t`, and the remaining `b` wires onto the complement `(insert
  t S)ᶜ`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {k b : ℕ}

/-- The complement `(insert t S)ᶜ` of the gate's support has exactly `b` wires (the number of
ambient wires the placed gate acts on as identity): `|(insert t S)ᶜ| = (k+1+b) - (k+1) = b`, using
`|insert t S| = |S| + 1 = k + 1` (as `t ∉ S`). -/
theorem card_compl_insert (S : Finset (Fin (k + 1 + b))) (t : Fin (k + 1 + b))
    (hk : S.card = k) (ht : t ∉ S) : (insert t S)ᶜ.card = b := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem ht, hk]; omega

/-- The piecewise **gather function** on `Fin (k + 1 + b)` underlying `wireGatherPerm`. -/
def gatherFun (S : Finset (Fin (k + 1 + b))) (t : Fin (k + 1 + b))
    (hk : S.card = k) (ht : t ∉ S) : Fin (k + 1 + b) → Fin (k + 1 + b) :=
  Fin.addCases
    (fun y => Fin.lastCases (motive := fun _ => Fin (k + 1 + b)) t
      (fun i => S.orderEmbOfFin hk i) y)
    (fun j => (insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht) j)

variable (S : Finset (Fin (k + 1 + b))) (t : Fin (k + 1 + b)) (hk : S.card = k) (ht : t ∉ S)

/-- `gatherFun` on a front control wire `Fin.castAdd b (Fin.castSucc i)` is the `i`-th element of
`S`. -/
theorem gatherFun_castAdd_castSucc (i : Fin k) :
    gatherFun S t hk ht (Fin.castAdd b (Fin.castSucc i)) = S.orderEmbOfFin hk i := by
  simp only [gatherFun, Fin.addCases_left, Fin.lastCases_castSucc]

/-- `gatherFun` on the front target wire `Fin.castAdd b (Fin.last k)` is the target `t`. -/
theorem gatherFun_castAdd_last :
    gatherFun S t hk ht (Fin.castAdd b (Fin.last k)) = t := by
  simp only [gatherFun, Fin.addCases_left, Fin.lastCases_last]

/-- `gatherFun` on a back wire `Fin.natAdd (k+1) j` is the `j`-th element of the complement. -/
theorem gatherFun_natAdd (j : Fin b) :
    gatherFun S t hk ht (Fin.natAdd (k + 1) j)
      = (insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht) j := by
  simp only [gatherFun, Fin.addCases_right]

/-- **`gatherFun` is injective.** Its three domain blocks (front controls, front target, back
wires) map to the three disjoint finsets `S`, `{t}`, `(insert t S)ᶜ`; a
`Fin.addCases`/`Fin.lastCases` case analysis closes cross-block cases by disjointness and same-block
cases by the injectivity of the order embeddings. -/
theorem gatherFun_injective : Function.Injective (gatherFun S t hk ht) := by
  have hAmem : ∀ i, S.orderEmbOfFin hk i ∈ S := fun i => Finset.orderEmbOfFin_mem S hk i
  have hCmem : ∀ j, (insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht) j ∈ (insert t S)ᶜ :=
    fun j => Finset.orderEmbOfFin_mem _ _ j
  intro x y hxy
  induction x using Fin.addCases with
  | left xl =>
    induction xl using Fin.lastCases with
    | last =>
      induction y using Fin.addCases with
      | left yl =>
        induction yl using Fin.lastCases with
        | last => rfl
        | cast yi =>
          rw [gatherFun_castAdd_last, gatherFun_castAdd_castSucc] at hxy
          exact absurd (hxy ▸ hAmem yi) ht
      | right yj =>
        rw [gatherFun_castAdd_last, gatherFun_natAdd] at hxy
        have hy := hCmem yj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hy
        exact absurd hxy.symm hy.1
    | cast xi =>
      induction y using Fin.addCases with
      | left yl =>
        induction yl using Fin.lastCases with
        | last =>
          rw [gatherFun_castAdd_castSucc, gatherFun_castAdd_last] at hxy
          exact absurd (hxy ▸ hAmem xi) ht
        | cast yi =>
          rw [gatherFun_castAdd_castSucc, gatherFun_castAdd_castSucc] at hxy
          have := (S.orderEmbOfFin hk).injective hxy
          rw [this]
      | right yj =>
        rw [gatherFun_castAdd_castSucc, gatherFun_natAdd] at hxy
        have hx : S.orderEmbOfFin hk xi ∈ S := hAmem xi
        have hy := hCmem yj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hy
        exact absurd (hxy ▸ hx) hy.2
  | right xj =>
    induction y using Fin.addCases with
    | left yl =>
      induction yl using Fin.lastCases with
      | last =>
        rw [gatherFun_natAdd, gatherFun_castAdd_last] at hxy
        have hx := hCmem xj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hx
        exact absurd hxy hx.1
      | cast yi =>
        rw [gatherFun_natAdd, gatherFun_castAdd_castSucc] at hxy
        have hy : S.orderEmbOfFin hk yi ∈ S := hAmem yi
        have hx := hCmem xj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hx
        exact absurd (hxy.symm ▸ hy) hx.2
    | right yj =>
      rw [gatherFun_natAdd, gatherFun_natAdd] at hxy
      have := ((insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht)).injective hxy
      rw [this]

/-- **The wire-gather permutation** of `Fin (k + 1 + b)` for a control set `S` (`S.card = k`) and
target `t ∉ S`: the bijectivisation of `gatherFun`. It gathers the `k` front control wires onto
`S`, the front target wire onto `t`, and the `b` back wires onto `(insert t S)ᶜ` — the permutation
to feed into `Evolution.placedMcCtrlX` to place a `Cᵏ(X)` on the prescribed wires `(S, t)`. -/
def wireGatherPerm : Equiv.Perm (Fin (k + 1 + b)) :=
  Equiv.ofBijective (gatherFun S t hk ht)
    (Finite.injective_iff_bijective.mp (gatherFun_injective S t hk ht))

end AxQM
