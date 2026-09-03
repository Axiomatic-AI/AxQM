/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotNetwork

/-!
# Concrete: the CNOT + Hadamard core of the stabilizer encoding circuit

The CNOT and Hadamard layers of the circuit of Nielsen & Chuang **Problem 10.3** ("encoding
stabilizer codes"), which carries the *trivial* check matrix `G` of Eq. (10.124) (a listing of the
single-qubit generators `Z₁, …, Zₙ`, i.e. every row `(0 | eᵢ)`) to the **standard form** of
Eq. (10.125).
-/

namespace AxQM.Concrete

variable {n : ℕ}

/-- **The combinatorial data of a standard-form stabilizer code** (N&C (10.111)/(10.125)), as
consumed by the encoding circuit. A partition of the `n` wires into `pivots` (the `r` generator
rows carrying an `X`-part), `middle` (the `n − k − r` pure-`Z` generator rows) and `dataWires`
(the `k` encoded-`Z` rows), together with a fan-target assignment `tgt : Fin n → List (Fin n)`
whose supports *are* the standard-form matrices. -/
structure StdFormData (n : ℕ) where
  /-- The pivot wires: the `r` generator rows with a nonzero `X`-part, Hadamard'd at the front. -/
  pivots : List (Fin n)
  /-- The middle wires: the `n − k − r` pure-`Z` generator rows. -/
  middle : List (Fin n)
  /-- The data wires: the `k` encoded-`Z` rows. -/
  dataWires : List (Fin n)
  /-- The CNOT-fan targets of each control wire (the supports of the `[A₁ | A₂]` / `E` rows). -/
  tgt : Fin n → List (Fin n)
  /-- The pivot control list has no repeats. -/
  pivots_nodup : pivots.Nodup
  /-- The data control list has no repeats. -/
  data_nodup : dataWires.Nodup
  /-- Every target list has no repeats (each `1` of a block gives one CNOT). -/
  tgt_nodup : ∀ w : Fin n, (tgt w).Nodup
  /-- A pivot's fan targets lie in the middle or data wires (the columns of `[A₁ | A₂]`). -/
  tgt_pivot_mem : ∀ p ∈ pivots, ∀ t ∈ tgt p, t ∈ middle ∨ t ∈ dataWires
  /-- A data wire's fan targets lie in the middle wires (the columns of `E`). -/
  tgt_data_mem : ∀ d ∈ dataWires, ∀ t ∈ tgt d, t ∈ middle
  /-- No pivot is a middle wire. -/
  pivot_not_middle : ∀ p ∈ pivots, p ∉ middle
  /-- No pivot is a data wire. -/
  pivot_not_data : ∀ p ∈ pivots, p ∉ dataWires
  /-- No data wire is a middle wire. -/
  data_not_middle : ∀ d ∈ dataWires, d ∉ middle

/-- **The CNOT + Hadamard core of the encoding circuit**: the Hadamard layer on
the pivots followed (in circuit order: acting after) by the CNOT network with control list
`pivots ++ dataWires`. Reading `act` right-to-left, the Hadamards act first (`Zₚ ↦ Xₚ`), then the
data-controlled `E`-fans, then the pivot fans. -/
def encodingCnotHad (D : StdFormData n) : CliffordCircuit n :=
  cnotNetwork (D.pivots ++ D.dataWires) D.tgt ++ hadLayer D.pivots

end AxQM.Concrete
