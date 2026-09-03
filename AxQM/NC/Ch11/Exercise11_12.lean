/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyComparisonState
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.Entropy
import Mathlib.Analysis.InnerProductSpace.PiL2
import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Nielsen & Chuang, Exercise 11.12 — comparison of quantum and classical entropies

*(N&C p. 511.)*

Evaluate S(rho) for a specific mixed qubit state and compare to H(p,1-p).

* `vonNeumannEntropy_entropyComparisonState` — evaluation. `S(ρ) = H((1 ± ‖r⃗‖)/2)`, the binary
  Shannon entropy of the two eigenvalues `(1 ± √((1 − p)² + p²))/2`.
* `vonNeumannEntropy_entropyComparisonState_le` — the comparison. `S(ρ) ≤ H(p, 1 − p)`: the quantum
  entropy never exceeds the classical Shannon entropy of the mixing weights.
* `vonNeumannEntropy_entropyComparisonState_lt` — the sharp comparison. For `0 < p < 1`, `S(ρ) <
  H(p, 1 − p)` *strictly*: the classical bound is not saturated because the two mixed states `|0⟩`
  and `|+⟩` are not orthogonal (equality `S(ρ) = H(p, 1 − p)` holds only at the endpoints `p ∈ {0,
  1}`, where `ρ` is pure).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **N&C Exercise 11.12, evaluation of `S(ρ)`.** For `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`, `S(ρ) =
H((1 + ‖r⃗‖)/2, (1 − ‖r⃗‖)/2)` with `‖r⃗‖ = √((1 − p)² + p²)`. -/
theorem vonNeumannEntropy_entropyComparisonState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (entropyComparisonState p hp0 hp1).vonNeumannEntropy
      = Real.entropy ![(1 + Real.sqrt ((1 - p) ^ 2 + p ^ 2)) / 2,
                       (1 - Real.sqrt ((1 - p) ^ 2 + p ^ 2)) / 2] := sorry

/-- **N&C Exercise 11.12, the comparison `S(ρ) ≤ H(p, 1 − p)`.** The von Neumann entropy of the
mixture `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|` never exceeds the classical Shannon entropy `H(p, 1 −
p)` of its mixing weights. -/
theorem vonNeumannEntropy_entropyComparisonState_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (entropyComparisonState p hp0 hp1).vonNeumannEntropy ≤ Real.entropy ![p, 1 - p] := sorry

/-- **N&C Exercise 11.12, the sharp comparison `S(ρ) < H(p, 1 − p)` for `0 < p < 1`.** Strictly
below the classical Shannon entropy: because `|0⟩` and `|+⟩` are non-orthogonal, mixing them loses
strictly less "information" than `H(p, 1 − p)`. The equality case `S(ρ) = H(p, 1 − p)` occurs only
at the endpoints `p ∈ {0, 1}` (where `ρ` is pure). Same route as the non-strict form, with the
strict `|2p − 1| < t` from `0 < 2p(1 − p)`. -/
theorem vonNeumannEntropy_entropyComparisonState_lt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (entropyComparisonState p hp0.le hp1.le).vonNeumannEntropy < Real.entropy ![p, 1 - p] := sorry

end AxQM
