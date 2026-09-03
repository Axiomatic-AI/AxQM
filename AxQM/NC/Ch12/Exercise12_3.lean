/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.Basic.PiTensor
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import AxQM.Basic.API.Entropy
import AxQM.NC.Ch12.Problem12_1

/-!
# Nielsen & Chuang, Exercise 12.3 (`n` qubits carry no more than `n` bits)

*(N&C p. 535.)*

Use Holevo bound to show n qubits carry no more than n bits of classical info.

* `mutualInfo_qubit_tensorPow_le` — the exercise's stated conclusion `H(X : Y) ≤ n · log 2`: Bob's
  classical information about Alice's message is at most `n` bits.
-/

namespace AxQM.State

/-- **Nielsen & Chuang, Exercise 12.3.** `n` qubits carry no more than `n` bits of classical
information. The classical mutual information Bob's outcome shares with Alice's message is at
most `n · log 2` — i.e. `n` bits:

`H(X : Y) ≤ n · log 2`,

where `H(X : Y) = Real.mutualInfo` of the joint distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ) = pₓ ·
m.bornProb ρₓ y` of Alice's message and Bob's outcome.
-/
theorem mutualInfo_qubit_tensorPow_le {ι : Type*} [Fintype ι] {n r : ℕ} [NeZero r]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State (qubit.tensorPow n)) (m : Measurement (Fin r) (qubit.tensorPow n)) :
    Real.mutualInfo (fun xy : ι × Fin r => p xy.1 * m.bornProb (ρ xy.1) xy.2)
      ≤ (n : ℝ) * Real.log 2 := sorry

end AxQM.State
