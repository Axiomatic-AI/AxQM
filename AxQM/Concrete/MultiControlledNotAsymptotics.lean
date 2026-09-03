/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotCircuit
import Mathlib.Tactic

/-!
# Concrete: the `Cⁿ(X)` gate count is `O(n²)` (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)`-gate no-work-qubit circuit
implementing the `n`-controlled `NOT` `Cⁿ(X)`. This file states the `O(n²)` reading of that gate
count.
-/

namespace AxQM.Concrete

open Filter Asymptotics

/-- **N&C Exercise 4.29, the `O(n²)` total gate count of the tight-register `Cⁿ(X)` circuit.** The
two elementary-gate counts of the Barenco no-work-qubit unfolding of `Cⁿ(X)` on exactly `n + 1`
wires — at most `8k(k+1)+2` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and at most `2k+3`
single-qubit gates — sum to `(8k(k+1)+2) + (2k+3)`, and that total is `O(n²)`:

`(fun k => (8k(k+1)+2)+(2k+3)) =O[atTop] (fun k => k²)`.

This is the pure `ℕ→ℝ` asymptotic reading Exercise 4.29 asks for.
-/
theorem barencoGateBudget_isBigO_sq :
    (fun k : ℕ => (((8 * k * (k + 1) + 2) + (2 * k + 3) : ℕ) : ℝ)) =O[atTop]
      fun k : ℕ => (k : ℝ) ^ 2 := sorry

end AxQM.Concrete
