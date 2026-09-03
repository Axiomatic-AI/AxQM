/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Concrete: the modular-addition permutation of a two-register basis

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.36 (p. 189) asks for a
circuit performing `|x, y⟩ → |x, x + y mod n⟩` (with `n = 4` for two-bit numbers). Writing the
two `n`-level registers' computational-basis labels as a pair `(x, y) : Fin n × Fin n`, the induced
permutation of the *joint* basis indices is `(x, y) ↦ (x, x + y)`.
-/

namespace AxQM.Concrete

/-- **The low (`2⁰`) binary digit** of a two-bit number `x : Fin 4`: `x % 2 ∈ {0, 1}`, the value
carried on the least-significant qubit when `x` is written in binary as `x = lowBit x + 2 · highBit
x`. -/
def lowBit (x : Fin 4) : Fin 2 := ⟨x.val % 2, by omega⟩

/-- **The high (`2¹`) binary digit** of a two-bit number `x : Fin 4`: `x / 2 ∈ {0, 1}`, the value
carried on the most-significant qubit when `x` is written in binary as `x = lowBit x + 2 · highBit
x`. -/
def highBit (x : Fin 4) : Fin 2 := ⟨x.val / 2, by have := x.isLt; omega⟩

end AxQM.Concrete
