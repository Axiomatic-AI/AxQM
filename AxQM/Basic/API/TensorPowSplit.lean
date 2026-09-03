/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.PiTensor
import AxQM.Basic.PiTensorState
import AxQM.Basic.API.SystemIsoComm

/-!
# AxQM.Basic.API — splitting a tensor power into factor blocks

Structural **system isomorphisms** regrouping the `n`-fold symmetric tensor power `S ^⊗ₛ n` into
sub-blocks of factors:

## Main declarations
* `QSystem.tensorPowSuccHead S n` — the head-peel isomorphism `S ^⊗ₛ (n+1) ≃ₛ S ⊗ (S ^⊗ₛ n)`,
  built from the fork's inner-product `PiTensorProduct` isometries: reindex `Fin (n+1)` as
  `Fin 1 ⊕ Fin n` (`reindexₗᵢ`), split the tensor along the `Sum` (`tmulEquivDepₗᵢ`), and collapse
  the singleton head factor `⨂ᵢ : Fin 1, S.space ≃ S.space` (`subsingletonEquivₗᵢ`).
* `QSystem.tensorPowOne S` — the one-factor collapse `S ≃ₛ S ^⊗ₛ 1` (the `n = 0` base of the
  `qtower`-bridge induction), from the subsingleton-index isometry
  `PiTensorProduct.subsingletonEquivₗᵢ`.
* `QSystem.blockSplit a b` — the index split `Fin (a+b) ≃ Fin a ⊕ Fin b` (`finSumFinEquiv.symm`)
  underlying the block isomorphism.
* `QSystem.tensorPowAdd S a b` — the **general block-split isomorphism**
  `S ^⊗ₛ (a+b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)`, grouping the first `a` factors into the left block and
  the last `b` into the right; built by reindexing along `QSystem.blockSplit a b` then the
  `Sum`-split `tmulEquivDepₗᵢ` (no singleton collapse — neither block is forced to be one factor).
* `QSystem.tensorPowCongr S e` — the **factor-relabelling isomorphism** `S ^⊗ₛ a ≃ₛ S ^⊗ₛ b` induced
  by a wire reindexing `e : Fin a ≃ Fin b`, the **constant-family case of the indexed reindex**
  `QSystem.piTensorReindex` (a thin named wrapper for the register-cast role). Unlike the block
  splits it does **not** regroup — same system, same factor count, only the wire labelling changes
  — so it is the general-arity companion of the wire-permutation gate `Evolution.permWires` (the
  `a = b`, `e : Equiv.Perm (Fin a)` case).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {n : ℕ}

/-- The index reshuffle `Fin (n + 1) ≃ Fin 1 ⊕ Fin n` underlying the head-peel isometry. -/
def QSystem.headSplit (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 1)).trans finSumFinEquiv.symm

/-- The head-peel underlying isometry `(S ^⊗ₛ (n+1)).space ≃ₗᵢ (S ⊗ S ^⊗ₛ n).space`. -/
noncomputable def QSystem.tensorPowSuccHeadIsometry (S : QSystem) (n : ℕ) :
    (⨂[ℂ] _ : Fin (n + 1), S.space) ≃ₗᵢ[ℂ] S.space ⊗[ℂ] (⨂[ℂ] _ : Fin n, S.space) :=
  (PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin (n + 1) => S.space) (QSystem.headSplit n)).trans
    ((PiTensorProduct.tmulEquivDepₗᵢ ℂ (fun _ : Fin 1 ⊕ Fin n => S.space)).symm.trans
      (TensorProduct.congrIsometry
        (PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun _ : Fin 1 => S.space) 0)
        (LinearIsometryEquiv.refl ℂ (⨂[ℂ] _ : Fin n, S.space))))

/-- **The head-peel system isomorphism** `S ^⊗ₛ (n+1) ≃ₛ S ⊗ (S ^⊗ₛ n)`: split the `(n+1)`-fold
tensor power into its head wire and the remaining `n`-fold power. The tensor-power `succ`
structural conversion, matching `qtower (n+1) S = S ⊗ qtower n S`. -/
def QSystem.tensorPowSuccHead (S : QSystem) (n : ℕ) : S ^⊗ₛ (n + 1) ≃ₛ S ⊗ S ^⊗ₛ n :=
  ⟨QSystem.tensorPowSuccHeadIsometry S n⟩

/-- **The one-factor collapse** `S ≃ₛ S ^⊗ₛ 1`: a single-factor tensor power is the system itself,
from the subsingleton-index isometry `PiTensorProduct.subsingletonEquivₗᵢ` over `Fin 1`. It is the
`n = 0` base case of the `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)` bridge (`Core`) — the analogue, at the
bottom of the induction, of `QSystem.tensorPowSuccHead` at each successor step. -/
def QSystem.tensorPowOne (S : QSystem) : S ≃ₛ S ^⊗ₛ 1 :=
  ⟨(PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun _ : Fin 1 => S.space) 0).symm⟩

/-- The index split `Fin (a + b) ≃ Fin a ⊕ Fin b` underlying the block-split isometry. -/
def QSystem.blockSplit (a b : ℕ) : Fin (a + b) ≃ Fin a ⊕ Fin b := finSumFinEquiv.symm

/-- The block-split underlying isometry `(S ^⊗ₛ (a+b)).space ≃ₗᵢ (S ^⊗ₛ a ⊗ S ^⊗ₛ
b).space`.

The reindex step carries an explicit codomain ascription `⨂[Fin a ⊕ Fin b] S.space`.
-/
noncomputable def QSystem.tensorPowAddIsometry (S : QSystem) (a b : ℕ) :
    (⨂[ℂ] _ : Fin (a + b), S.space) ≃ₗᵢ[ℂ]
      (⨂[ℂ] _ : Fin a, S.space) ⊗[ℂ] (⨂[ℂ] _ : Fin b, S.space) :=
  ((PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin (a + b) => S.space) (QSystem.blockSplit a b) :
      (⨂[ℂ] _ : Fin (a + b), S.space) ≃ₗᵢ[ℂ] ⨂[ℂ] _ : Fin a ⊕ Fin b, S.space)).trans
    (PiTensorProduct.tmulEquivDepₗᵢ ℂ (fun _ : Fin a ⊕ Fin b => S.space)).symm

set_option maxHeartbeats 1000000 in
-- The `QSystem.Iso` ⟨⟩ constructor checks the raw isometry's space types against
-- `(S ^⊗ₛ (a+b)).space` / `((S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)).space`; unfolding `piTensor.space` at the
-- *symbolic* index `a + b` is markedly heavier than at the numeral `n + 1` of `tensorPowSuccHead`
-- (but finite — a plain defeq, not a loop), so the default heartbeat budget is raised for it.
/-- **The block-split system isomorphism** `S ^⊗ₛ (a + b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)`: split the
`(a+b)`-fold tensor power into its first `a` factors and its last `b` factors. The general-arity
tensor-power split, generalising the `succ` head-peel `QSystem.tensorPowSuccHead` (the `a = 1`
case, up to the singleton collapse of the head factor). -/
def QSystem.tensorPowAdd (S : QSystem) (a b : ℕ) : S ^⊗ₛ (a + b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b) :=
  ⟨QSystem.tensorPowAddIsometry S a b⟩

/-- **The factor-relabelling system isomorphism** `S ^⊗ₛ a ≃ₛ S ^⊗ₛ b` induced by a wire reindexing
`e : Fin a ≃ Fin b`.

It is the **constant-family case of the indexed reindex** `QSystem.piTensorReindex`: since `S
^⊗ₛ a = ⨂ₛ _ : Fin a, S`, reindexing the constant family `fun _ : Fin a => S` along `e` lands on
`⨂ₛ _ : Fin b, S = S ^⊗ₛ b`.

Its role in Exercise 4.29 is the **register cast**.
-/
def QSystem.tensorPowCongr (S : QSystem) {a b : ℕ} (e : Fin a ≃ Fin b) : S ^⊗ₛ a ≃ₛ S ^⊗ₛ b :=
  QSystem.piTensorReindex e (fun _ : Fin a => S)

end AxQM
