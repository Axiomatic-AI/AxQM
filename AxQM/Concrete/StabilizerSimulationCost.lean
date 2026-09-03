/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit

/-!
# Concrete: the Gottesman–Knill efficiency bound — `O(n²m)` classical simulation cost

The **efficiency bound** of the Gottesman–Knill theorem (Nielsen & Chuang **Theorem 10.7**,
§10.5.4, p. 464).
-/

namespace AxQM.Concrete

variable {n : ℕ}

/-- An **operation of a stabiliser computation** on the `n`-qubit register: exactly the elements
Nielsen & Chuang **Theorem 10.7** allows.

* `prep` — preparation of the computational-basis state (reset the tracked stabiliser to the trivial
  `⟨Z₁, …, Zₙ⟩`);
* `clifford g` — a Hadamard, phase (`S`), or controlled-`NOT` gate (the elementary Clifford gates
  `Concrete.CliffordGate n`);
* `pauli p` — a Pauli gate: the Pauli operator with Pauli string `p : Fin n → Fin 4` applied as a
  unitary (its tableau action changes only generator signs);
* `measure p` — a measurement of the Pauli-group observable with Pauli string `p`.

A computation is a finite sequence of these (`StabilizerComputation`), and the Gottesman–Knill
theorem asserts each is classically simulable in `O(n²)` steps. -/
inductive StabilizerOp (n : ℕ) : Type where
  /-- Prepare the computational-basis state (reset to the trivial stabiliser `⟨Z₁, …, Zₙ⟩`). -/
  | prep : StabilizerOp n
  /-- Apply an elementary Clifford gate (Hadamard, phase, or controlled-`NOT`). -/
  | clifford (g : CliffordGate n) : StabilizerOp n
  /-- Apply the Pauli gate with Pauli string `p`. -/
  | pauli (p : Fin n → Fin 4) : StabilizerOp n
  /-- Measure the Pauli-group observable with Pauli string `p`. -/
  | measure (p : Fin n → Fin 4) : StabilizerOp n

/-- A **stabiliser computation** on the `n`-qubit register: the finite sequence of `m` operations
(`StabilizerOp n`) actually executed. -/
abbrev StabilizerComputation (n : ℕ) : Type := List (StabilizerOp n)

/-- The **classical cost of simulating one operation**: the number of elementary tableau-cell
updates the standard generator-tracking simulator performs. The stabiliser of an `n`-qubit state is
tracked as `n` generators, each an `n`-qubit Pauli string (`n` Pauli cells) with a `±1` sign, so a
full pass over the tableau costs `n · (n + 1)`.

* `prep`, `clifford`, `pauli` — one pass updating all `n` generators: `n · (n + 1)`.
* `measure` — a commutation-scan pass (which generators anticommute with the measured observable)
  followed by an update pass: `2 · n · (n + 1)`.

Every value is `≤ 4 · n²` — N&C's uniform "`O(n²)` steps per operation". -/
def StabilizerOp.tableauCost : StabilizerOp n → ℕ
  | .prep => n * (n + 1)
  | .clifford _ => n * (n + 1)
  | .pauli _ => n * (n + 1)
  | .measure _ => 2 * (n * (n + 1))

/-- The **total classical cost of simulating a stabiliser computation**: the sum of the
per-operation tableau-update costs `StabilizerOp.tableauCost`.
-/
def StabilizerComputation.simCost (prog : StabilizerComputation n) : ℕ :=
  (prog.map StabilizerOp.tableauCost).sum

/-- **The Gottesman–Knill efficiency theorem (N&C Theorem 10.7, the `O(n²m)` bound).** There is a
*universal* constant `K` such that every stabiliser computation `prog` of `m =
prog.length` operations on `n` qubits is classically simulated in at most `K · n² · m`
elementary tableau updates: `∃ K, ∀ n (prog : StabilizerComputation n), simCost prog ≤ K · n² ·
prog.length`.
-/
theorem exists_simCost_le_mul_sq_length :
    ∃ K, ∀ (n : ℕ) (prog : StabilizerComputation n),
      StabilizerComputation.simCost prog ≤ K * n ^ 2 * prog.length := sorry

end AxQM.Concrete
