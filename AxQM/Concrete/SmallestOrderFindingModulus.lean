/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.NumberTheory.PerfectPower
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete: `15` is the smallest modulus requiring the order-finding subroutine

Nielsen & Chuang, Exercise 5.19 (§5.3.2, p. 234): `15` is the least modulus for which the
order-finding subroutine is required, i.e. the least composite that is neither even nor a power of
a smaller integer.
-/

namespace AxQM.Concrete

/-- **The order-finding class (Nielsen & Chuang, §5.3.2).** A modulus `n` genuinely requires the
quantum order-finding subroutine — it survives both classical pre-steps of the factoring reduction —
precisely when it is composite (`1 < n` and not prime), **odd** (`¬ Even n`, escaping step 1's
factor of `2`), and **not a perfect power** (`¬ n.IsPerfectPower`, escaping step 2's `a ^ b` test of
Exercise 5.17). Exercise 5.19 asks for the least such `n`. -/
def NeedsOrderFinding (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ¬ Even n ∧ ¬ n.IsPerfectPower

/-- **Nielsen & Chuang, Exercise 5.19.** `15` is the smallest number requiring the order-finding
subroutine — the least composite that is odd and not a perfect power. -/
theorem isLeast_needsOrderFinding : IsLeast {n | NeedsOrderFinding n} 15 := sorry

end AxQM.Concrete
