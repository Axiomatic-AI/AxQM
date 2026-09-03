/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.ZMod.Basic

/-!
# Concrete: the order-finding orbit index `x^k mod N`

For a unit `x` of `ZMod N` (a residue coprime to `N`) of multiplicative order `r = orderOf x`, the
computational-basis index of the orbit point `x^k mod N`, as an element of `Fin N`. This is the pure
`ZMod`/`Fin` combinatorics underlying Nielsen & Chuang's order-finding register (§5.3.1): the basis
states `|x^k mod N⟩` on which the order-finding eigenstates `|u_s⟩` are built, and which the
modular-multiplication unitary `U|y⟩ = |xy mod N⟩` permutes.

## Main declarations
* `orbitIndex x k` — the index `x^k mod N : Fin N`.
* `orbitIndex_fin_injective` — the `r` orbit points `{x^k mod N : k < r}` are distinct.
* `orbitIndex_mod` — `x^k mod N` is `r`-periodic in `k`.
-/

namespace AxQM.Concrete

/-- The computational-basis index `x^k mod N : Fin N` of the `k`-th orbit point of a unit `x` of
`ZMod N` — the state `|x^k mod N⟩` of Nielsen & Chuang's order-finding register `qudit N`. -/
def orbitIndex {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (k : ℕ) : Fin N :=
  ⟨((x : ZMod N) ^ k).val, ZMod.val_lt _⟩

/-- The orbit points `{x^k mod N : k < r}` are distinct: `k ↦ x^k mod N` is injective on
`Fin (orderOf x)`. -/
theorem orbitIndex_fin_injective {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) :
    Function.Injective (fun k : Fin (orderOf x) => orbitIndex x (k : ℕ)) := by
  intro a b hab
  simp only [orbitIndex, Fin.mk.injEq] at hab
  have hpow : (x : ZMod N) ^ (a : ℕ) = (x : ZMod N) ^ (b : ℕ) := ZMod.val_injective N hab
  have ha : (a : ℕ) ∈ Set.Iio (orderOf (x : ZMod N)) := by
    rw [Set.mem_Iio, orderOf_units]; exact a.isLt
  have hb : (b : ℕ) ∈ Set.Iio (orderOf (x : ZMod N)) := by
    rw [Set.mem_Iio, orderOf_units]; exact b.isLt
  exact Fin.ext (pow_injOn_Iio_orderOf ha hb hpow)

/-- `x^k mod N` is `r`-periodic in the exponent. -/
theorem orbitIndex_mod {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (k : ℕ) :
    orbitIndex x (k % orderOf x) = orbitIndex x k := by
  apply Fin.ext
  change ((x : ZMod N) ^ (k % orderOf x)).val = ((x : ZMod N) ^ k).val
  rw [← orderOf_units, pow_mod_orderOf]

end AxQM.Concrete
