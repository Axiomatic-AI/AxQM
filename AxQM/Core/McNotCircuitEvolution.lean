/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.WireGatherPermutation
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.LeftPairGate

/-!
# A classical `mcNot` circuit as an `Evolution` (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. A classical circuit is a `List` of gates
`gs : List (McNotGate m)` — each gate `(Sᵢ, tᵢ)` a wire-addressed multiply-controlled `NOT`
`Concrete.mcNot Sᵢ tᵢ` with `|Sᵢ| ≤ 2` — with composite denotation `Concrete.mcNotDenote gs` the
reversible bit-string permutation `Cⁿ(X)`. Its gates all act on the **one ambient register**
`qubit ^⊗ₛ m`.

## Main declarations
* `Evolution.placedMcNot S t ht` — a single classical gate `(S, t)` (`t ∉ S`) realised as a genuine
  `Evolution (qubit ^⊗ₛ m)` on the **ambient** register.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {m : ℕ}

/-- **The gate-local register matches the ambient register.** For a gate `(S, t)` with `t ∉ S` on
`Fin m`, the support `insert t S` uses `|S| + 1 ≤ m` wires, so the gate-local wire count
`|S| + 1 + (m - (|S| + 1))` (the `Evolution.placedMcCtrlX` register arity) is exactly `m`. -/
theorem card_succ_add_sub (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S) :
    S.card + 1 + (m - (S.card + 1)) = m := by
  have h : S.card + 1 ≤ m := by
    have hle := Finset.card_le_univ (insert t S)
    rwa [Finset.card_insert_of_notMem ht, Fintype.card_fin] at hle
  omega

/-- **A single classical `mcNot` gate placed on the ambient register.** Given a control set `S :
Finset (Fin m)` and target `t ∉ S`, the multiply-controlled `NOT` gate `(S, t)` realised as a
genuine closed-system `Evolution (qubit ^⊗ₛ m)` on the whole ambient register. For `|S| ≤ 2`
this is a `Toffoli`/`CNOT`/`NOT` addressed to the wires `(S, t)`. -/
def Evolution.placedMcNot (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S) :
    Evolution (qubit ^⊗ₛ m) :=
  (Evolution.placedMcCtrlX S.card (m - (S.card + 1))
      (wireGatherPerm (S.map (finCongr (card_succ_add_sub S t ht)).symm.toEmbedding)
        ((finCongr (card_succ_add_sub S t ht)).symm t)
        (by rw [Finset.card_map])
        (by
          intro hmem
          rw [Finset.mem_map] at hmem
          obtain ⟨x, hx, hxe⟩ := hmem
          rw [Equiv.coe_toEmbedding] at hxe
          exact ht ((finCongr (card_succ_add_sub S t ht)).symm.injective hxe ▸ hx)))).congr
    (QSystem.tensorPowCongr qubit (finCongr (card_succ_add_sub S t ht)))

end AxQM
