/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Concrete: concatenating two `[n, 1]` stabilizer codes

The **explicit generator construction** for the concatenation of two stabilizer codes (Nielsen &
Chuang, Exercise 10.62).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι]

/-- An **`[n, 1]` stabilizer code with a chosen logical `X̄`/`Z̄` pair**, on `n = g + 1` qubits with
`g` generators — the data N&C's construction consumes. `gen` are `g` phase-free Pauli-string
generators; they **commute** (`gen_commute`) and are **independent** (`gen_indep`: their check
rows are `𝔽₂`-linearly independent, N&C Prop 10.3), so `⟨gen⟩` is an `[g+1, 1]` stabilizer (`k =
1`). The logical operators `logX`, `logZ` lie in the normalizer — each **commutes** with every
generator (`logX_commute`, `logZ_commute`) — and form a **hyperbolic pair**. -/
structure StabCode1 (g : ℕ) where
  /-- The `g = n − 1` phase-free stabilizer generators on `n = g + 1` qubits. -/
  gen : Fin g → (Fin (g + 1) → Fin 4)
  /-- The logical `X̄` operator. -/
  logX : Fin (g + 1) → Fin 4
  /-- The logical `Z̄` operator. -/
  logZ : Fin (g + 1) → Fin 4
  /-- The generators pairwise commute. -/
  gen_commute : ∀ i j, Commute (pauliString (gen i)) (pauliString (gen j))
  /-- The generators are independent: their check rows are `𝔽₂`-linearly independent (Prop 10.3). -/
  gen_indep : LinearIndependent (ZMod 2) (fun i => checkRow (gen i))
  /-- `X̄` commutes with every generator (it is in the normalizer). -/
  logX_commute : ∀ i, Commute (pauliString logX) (pauliString (gen i))
  /-- `Z̄` commutes with every generator (it is in the normalizer). -/
  logZ_commute : ∀ i, Commute (pauliString logZ) (pauliString (gen i))
  /-- `X̄` and `Z̄` anticommute (they form a hyperbolic logical pair). -/
  logXZ_anticommute : ¬ Commute (pauliString logX) (pauliString logZ)

variable {g₁ g₂ : ℕ}

/-- The **encoded single-qubit Pauli** `p` for the code `C`: the inner logical operator
`X̄^{x} Z̄^{z}` (with `(x, z) = pauliBit p`) realizing `p` on an encoded block. `I ↦ 𝟙`, `X ↦ X̄`,
`Z ↦ Z̄`, `Y ↦ X̄ Z̄`. -/
def encStr (C : StabCode1 g₁) (p : Fin 4) : Fin (g₁ + 1) → Fin 4 :=
  if pauliXBit p = 0 then
    (if pauliZBit p = 0 then (fun _ => 0) else C.logZ)
  else
    (if pauliZBit p = 0 then C.logX else pauliMulIndex C.logX C.logZ)

/-- The **index set of the concatenated generators**: `n₂ = g₂ + 1` blocks each carrying `g₁` inner
generators (`inl (b, a)`), plus `g₂` encoded outer generators (`inr j`). -/
abbrev ConcatIdx (g₁ g₂ : ℕ) : Type := (Fin (g₂ + 1) × Fin g₁) ⊕ Fin g₂

/-- **The concatenated stabilizer generators, on the product qubit index** `Fin (g₂+1) × Fin (g₁+1)`
(block, inner qubit). -/
def concatRaw (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    ConcatIdx g₁ g₂ → (Fin (g₂ + 1) × Fin (g₁ + 1) → Fin 4)
  | Sum.inl (b, a) => fun q => if q.1 = b then C₁.gen a q.2 else 0
  | Sum.inr j => fun q => encStr C₁ (C₂.gen j q.1) q.2

/-- **The concatenated stabilizer generators on the flattened `Fin (n₁n₂)` register**, obtained from
`concatRaw` by identifying `Fin (g₂+1) × Fin (g₁+1) ≃ Fin ((g₂+1)(g₁+1))` (`finProdFinEquiv`). -/
def concatGen (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    ConcatIdx g₁ g₂ → (Fin ((g₂ + 1) * (g₁ + 1)) → Fin 4) :=
  fun c => concatRaw C₁ C₂ c ∘ finProdFinEquiv.symm

/-- **The concatenated code has `n₁n₂ − 1` generators**: the index set has cardinality
`(g₂+1) · g₁ + g₂ = (g₂+1)(g₁+1) − 1 = n₁n₂ − 1`. Together with the `n₁n₂` qubits this is the
`[n₁n₂, 1]` parameter count (`n₁n₂ − (n₁n₂ − 1) = 1`). -/
theorem concatIdx_card : Fintype.card (ConcatIdx g₁ g₂) = (g₂ + 1) * (g₁ + 1) - 1 := by
  simp only [ConcatIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega

end AxQM.Concrete
