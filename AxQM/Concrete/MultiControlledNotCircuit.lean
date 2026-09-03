/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNot
import Mathlib.Data.Fintype.Card

/-!
# Concrete: circuits of multiply-controlled `NOT` gates

Gates of a multiply-controlled-`NOT` circuit and their denotation, for Nielsen & Chuang,
Exercise 4.29 (p. 184): a circuit of `Toffoli`, `CNOT` and single-qubit (`NOT`) gates implementing
the `n`-controlled `NOT` `Cⁿ(X)`, with every gate at most twice-controlled and no *clean* work
qubit.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-- A single reversible gate of a multiply-controlled-`NOT` circuit: the control set together with
the target wire, denoting the classical gate `mcNot S t`. With `|S| ≤ 2` this is a `Toffoli`
(`|S| = 2`), `CNOT` (`|S| = 1`), or `NOT` (`|S| = 0`). -/
abbrev McNotGate (m : ℕ) : Type := Finset (Fin m) × Fin m

/-- **Denotation of a gate circuit**. -/
def mcNotDenote (gs : List (McNotGate m)) (x : Fin m → Fin 2) : Fin m → Fin 2 :=
  gs.foldr (fun g y => mcNot g.1 g.2 y) x

end AxQM.Concrete
