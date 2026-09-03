/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerIndependence
import Mathlib.LinearAlgebra.StdBasis

/-!
# Concrete: Nielsen & Chuang Exercise 10.53 — the encoded `Z` operators are independent

Nielsen & Chuang, **Exercise 10.53** (§10.5.7, p. 471): the `k` encoded `Z` operators read off the
*standard form* of a stabilizer code's check matrix are **independent of one another**.
-/

open scoped Matrix

namespace AxQM.Concrete

variable {r k : ℕ}

/-- The **pure-`Z` Pauli-string index** with support `w`: `Z` (index `3`) on each qubit `q` where
`w q ≠ 0`, and `I` (index `0`) elsewhere. Its check row is `(0 | w)`: an all-`Z` string has no
`X`-part, and its `Z`-part is exactly the support `w`. -/
def zIndexOf {n : ℕ} (w : Fin n → ZMod 2) : Fin n → Fin 4 := fun q => if w q = 0 then 0 else 3

/-- The **`Z`-support of the `j`-th encoded `Z` operator**, i.e. the `j`-th row of the `Z`-part
`[A₂ᵀ 0 I]` of the encoded-`Z` check matrix (Nielsen & Chuang §10.5.7): the transpose column
`A₂ᵀ_{j·} = (i ↦ A₂ i j)` on the first `r` qubits, `0` on the middle `s = n − k − r` qubits, and the
standard basis vector `eⱼ = Pi.single j 1` (the identity block) on the last `k` data qubits. -/
def encodedZRow (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) (j : Fin k) :
    Fin (r + s + k) → ZMod 2 :=
  Fin.append (Fin.append (fun i => A₂ i j) (0 : Fin s → ZMod 2)) (Pi.single j 1)

/-- The **`j`-th encoded `Z` operator** of a standard-form `[n, k]` code (Nielsen & Chuang §10.5.7),
as an `n`-qubit Pauli-group element (`n = r + s + k`): the pure product of `Z`'s with phase `1` and
`Z`-support `encodedZRow s A₂ j`. -/
def encodedZOp (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) (j : Fin k) :
    PauliGroup (r + s + k) :=
  ⟨0, zIndexOf (encodedZRow s A₂ j)⟩

/-- **Nielsen & Chuang, Exercise 10.53.** The `k` encoded `Z` operators of a standard-form `[n, k]`
stabilizer code are **independent of one another** (`IndependentGenerators`, N&C eq. 10.82: dropping
any one strictly shrinks the group generated). -/
theorem encodedZOp_independentGenerators (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) :
    IndependentGenerators (encodedZOp s A₂) := sorry

end AxQM.Concrete
