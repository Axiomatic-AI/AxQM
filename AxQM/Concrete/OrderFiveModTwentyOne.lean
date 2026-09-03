/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Concrete: the order of `5` modulo `21` is `6`

Nielsen & Chuang, Exercise 5.10 (§5.3.1, p. 226) asks for the order of `x = 5` modulo
`N = 21`. The **order of `x` modulo `N`** is, by definition, the least positive integer
`r` with `x^r ≡ 1 (mod N)` — equivalently the multiplicative order of the residue `x` in the ring
`ZMod N`, i.e. Mathlib's `orderOf (x : ZMod N)`.
-/

namespace AxQM.Concrete

/-- **Nielsen & Chuang, Exercise 5.10.** The multiplicative order of `5` modulo `21` is `6`: `6` is
the least positive integer `r` with `5^r ≡ 1 (mod 21)`.
-/
theorem orderOf_five_zmod_twentyOne : orderOf (5 : ZMod 21) = 6 := sorry

end AxQM.Concrete
