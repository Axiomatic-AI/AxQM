/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.LeftPairGate

/-!
# AxQM.Basic.API — a single-qubit/`CNOT` circuit for a two-level unitary (N&C Ex 4.39)

Infrastructure for **Nielsen & Chuang, Exercise 4.39** (§4.5.2, p. 193): a circuit
built from single-qubit and `CNOT` gates that implements the three-qubit *two-level* unitary
(eq. 4.60)

## Main declarations
* `twoLevelRoute` — the routing permutation `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂ ⊕ q₃, q₂, q₃⟩`, a product of
  three `CNOT`s.
* `twoLevelUnitaryCircuit Ũ` — the circuit `W · C²(Ũ) · W` on `qubit ⊗ (qubit ⊗ qubit)`.
* `twoLevelUnitaryCircuit_evolvePure_inactive` — the six computational-basis states other than
 `|010⟩` and `|111⟩` are fixed (the identity blocks of (4.60)), a statement.
* `twoLevelUnitaryCircuit_evolvePure_active_ketZero` / `..._active_ketOne` — the coupled pair:
  `U|010⟩ = a • |010⟩ + b • |111⟩` and `U|111⟩ = c • |010⟩ + d • |111⟩`, where the entries
  `a, b, c, d` of `Ũ` are read off from its action `Ũ|0⟩ = a|0⟩ + b|1⟩`, `Ũ|1⟩ = c|0⟩ + d|1⟩` (the
  two columns of `Ũ`). These are exactly columns 2 and 7 of (4.60).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The routing permutation** `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂ ⊕ q₃, q₂, q₃⟩` on
`qubit ⊗ (qubit ⊗ qubit)`, a product of three `CNOT`s
(`reversedCNOT₃→₂ · reversedCNOT₂→₁ · reversedCNOT₃→₂`) that XORs `q₂ ⊕ q₃` into qubit 1. It is an
involution and relabels the adjacent pair `{|110⟩, |111⟩}` (on which `C²(Ũ)` acts) to the target
pair `{|010⟩, |111⟩}` of (4.60): `|010⟩ ↔ |110⟩`, `|111⟩` fixed. -/
def twoLevelRoute : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (reversedCnotGate.onRight qubit).comp
    (reversedCnotLeftGate.comp (reversedCnotGate.onRight qubit))

/-- **The Exercise 4.39 circuit.** The two-level unitary (4.60) on `qubit ⊗ (qubit ⊗ qubit)`, built
as the doubly-controlled gate `C²(Ũ) = ccontrolledUnitary Ũ` conjugated by the routing permutation
`twoLevelRoute`: `twoLevelUnitaryCircuit Ũ = W · C²(Ũ) · W`. Built from single-qubit and `CNOT`
gates (three `CNOT`s in each `W`, and `C²(Ũ)` decomposes further, Exercise 4.22). -/
def twoLevelUnitaryCircuit (u : Evolution qubit) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  twoLevelRoute.comp ((ccontrolledUnitary u).comp twoLevelRoute)

/-- **The inactive block of (4.60).** Every computational-basis state other than the coupled pair
`|010⟩`, `|111⟩` is left unchanged by the circuit: for `(q₁, q₂, q₃) ≠ (0, 1, 0)` and `≠ (1, 1,
1)`, `twoLevelUnitaryCircuit Ũ |q₁, q₂, q₃⟩ = |q₁, q₂, q₃⟩`. These are the six identity columns
of (4.60). -/
theorem twoLevelUnitaryCircuit_evolvePure_inactive (u : Evolution qubit) (q1 q2 q3 : Fin 2)
    (h : ¬ (q1 = 0 ∧ q2 = 1 ∧ q3 = 0) ∧ ¬ (q1 = 1 ∧ q2 = 1 ∧ q3 = 1)) :
    (twoLevelUnitaryCircuit u).evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)) := sorry

/-- **Column 2 of (4.60):** the circuit sends `|010⟩` to `a • |010⟩ + b • |111⟩`, where `a, b` are
the first column of `Ũ` (`Ũ|0⟩ = a|0⟩ + b|1⟩`). Routing sends `|010⟩ ↦ |110⟩`, then `C²(Ũ)` applies
`Ũ` to qubit 3 giving `|11⟩ ⊗ Ũ|0⟩`; expanding `Ũ|0⟩ = a|0⟩ + b|1⟩` and routing back (linearly)
lands on `a • |010⟩ + b • |111⟩`. -/
theorem twoLevelUnitaryCircuit_evolvePure_active_ketZero (u : Evolution qubit) (a b : ℂ)
    (hu0 : (u.evolvePure (qubitBasis 0)).vec
      = a • (qubitBasis 0).vec + b • (qubitBasis 1).vec) :
    ((twoLevelUnitaryCircuit u).evolvePure
        ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0)))).vec
      = a • ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec
        + b • ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := sorry

/-- **Column 7 of (4.60):** the circuit sends `|111⟩` to `c • |010⟩ + d • |111⟩`, where `c, d` are
the second column of `Ũ` (`Ũ|1⟩ = c|0⟩ + d|1⟩`). Routing fixes `|111⟩`, then `C²(Ũ)` applies `Ũ` to
qubit 3 giving `|11⟩ ⊗ Ũ|1⟩`; expanding `Ũ|1⟩ = c|0⟩ + d|1⟩` and routing back lands on
`c • |010⟩ + d • |111⟩`. -/
theorem twoLevelUnitaryCircuit_evolvePure_active_ketOne (u : Evolution qubit) (c d : ℂ)
    (hu1 : (u.evolvePure (qubitBasis 1)).vec
      = c • (qubitBasis 0).vec + d • (qubitBasis 1).vec) :
    ((twoLevelUnitaryCircuit u).evolvePure
        ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1)))).vec
      = c • ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec
        + d • ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := sorry

end AxQM
