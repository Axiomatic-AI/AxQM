/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNot

/-!
# Concrete: the back-pair wire-gather permutation

Pure `Fin`/`Equiv` combinatorics for **addressing a two-qubit gate to an arbitrary ordered wire
pair**.  To place a gate whose canonical form acts on the *last two* wires `(n, n+1)` of an
`(n+2)`-wire register onto a chosen ordered pair `(i, j)`, one relabels the wires by a permutation
`σ` with `σ (wire n) = i` (the control) and `σ (wire n+1) = j` (the target); the remaining `n` wires
map onto `{i, j}ᶜ` in some order (their identity is immaterial).
-/

namespace AxQM.Concrete

/-- **The back-pair wire-gather permutation** of `Fin (n+2)` sending the last-two-wire positions
`(Fin.natAdd n 0, Fin.natAdd n 1)` — wires `n` and `n+1` — to a designated ordered pair `(i, j)`:
`(Equiv.swap n i).trans (Equiv.swap ((Equiv.swap n i) (n+1)) j)`.  The first transposition carries
`n ↦ i`; the second carries the image of `n+1` to `j` while fixing `i` (when `i ≠ j`).  So
`σ (wire n) = i` (for `i ≠ j`) and `σ (wire n+1) = j`; the other `n` wires map onto `{i, j}ᶜ`. -/
def cnotPairGatherPerm (n : ℕ) (i j : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (Equiv.swap (Fin.natAdd n 0) i).trans
    (Equiv.swap ((Equiv.swap (Fin.natAdd n 0) i) (Fin.natAdd n 1)) j)

end AxQM.Concrete
