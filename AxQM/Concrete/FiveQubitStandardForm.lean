/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.FiveQubitCode
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: the five-qubit code check matrix in standard form (Nielsen & Chuang, Exercise 10.57)

The check matrix of the five-qubit code in standard form: Nielsen & Chuang, **Exercise 10.57** —
*give the check matrices for the five and nine qubit codes in standard form* (N&C §10.5.7, p. 472).

## Main results
* `fiveQubitStdGen` — the four standard-form generators, as `Fin 5 → Fin 4` Pauli-index strings
  (`I=0, X=1, Y=2, Z=3`): **the check matrix in standard form**.
* `fiveQubitStdGen_xPart_pivot_identity` — the certificate that it **is in standard form**: the
  `X`-part restricted to the first `r = 4` (pivot) columns is the `4 × 4` identity `I₄`.
* `fiveQubitStdGen_checkRow_span_eq` — the certificate that it is **the same code**: the `𝔽₂`-span
  of the standard-form check rows equals that of the original Figure-10.12 generators' check rows
  (no qubit relabeling is needed here). Since a stabilizer code is exactly the row space of its
  check matrix, this says the standard form and the textbook generators define the same five-qubit
  code.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

/-- **The five-qubit code check matrix in standard form** (Nielsen & Chuang, Exercise 10.57), as
four `Fin 5 → Fin 4` Pauli-index strings (`I=0, X=1, Y=2, Z=3`):
```
s₁ = Y Z I Z Y      s₃ = Z Z X I X
s₂ = I X Z Z X      s₄ = Z I Z Y Y
```
The `X`-part is `[I₄ | A₂]`, so `r = 4`, `m = 0`, `k = 1` (no `[0 0 0 | D I E]` block, no qubit
swap). -/
def fiveQubitStdGen : Fin 4 → Fin 5 → Fin 4 :=
  ![![2, 3, 0, 3, 2], ![0, 1, 3, 3, 1], ![3, 3, 1, 0, 1], ![3, 0, 3, 2, 2]]

/-- **The five-qubit standard form is in standard form** (N&C eq. (10.111)): the `X`-part of the
check matrix, restricted to the first `r = 4` (pivot) columns, is the `4 × 4` identity — row `i` has
a `1` in pivot column `j` iff `i = j`. Since `m = n − k − r = 0` there is no middle block and no
bottom `[0 0 0 | D I E]` rows, so this identity block is the full standard-form shape condition on
the `X`-part. -/
theorem fiveQubitStdGen_xPart_pivot_identity (i : Fin 4) (j : Fin 5) (hj : j.val ≤ 3) :
    (checkRow (fiveQubitStdGen i)).1 j = if i.val = j.val then 1 else 0 := sorry

/-- **Nielsen & Chuang, Exercise 10.57 (five-qubit code): the standard form defines the same code.**
The `𝔽₂`-span of the standard-form check rows `fiveQubitStdGen` equals the span of the original
Figure-10.12 generators' check rows.
-/
theorem fiveQubitStdGen_checkRow_span_eq :
    Submodule.span (ZMod 2) (Set.range (fun i => checkRow (fiveQubitStdGen i)))
      = Submodule.span (ZMod 2) (Set.range (fun i => checkRow (fiveQubitGenIdx i))) := sorry

end AxQM.Concrete
