/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HammingCode743
import AxQM.ToMathlib.InformationTheory.Coding.DualCode

/-!
# Concrete: the dual `[7, 3]` Hamming code `C₂ = C⊥` of the Steane construction

The classical code `C₂ = C⊥` of the Steane construction (Nielsen & Chuang, Exercise 10.32).

## Main results

* `steaneDualCode` — the dual code `C₂ = C⊥`.
* `one_mem_ofParityCheck_hammingParityCheck` — the all-ones word `𝟙` is a Hamming codeword.
* `steaneDualCode_dotProduct_one` — every dual codeword has even weight.
-/

namespace AxQM.Concrete

open Matrix

/-- The **dual `[7, 3]` Hamming code** `C₂ = C⊥` of the Steane construction (Nielsen & Chuang,
§10.4.2). Its eight codewords are the kets summed in the Steane `|0_L⟩` (eq. 10.78). -/
noncomputable def steaneDualCode : LinearCode (ZMod 2) (Fin 7) :=
  LinearCode.dual (LinearCode.ofParityCheck hammingParityCheck)

noncomputable instance : DecidablePred (· ∈ steaneDualCode) := Classical.decPred _

/-- **The all-ones word `𝟙` is a Hamming codeword** (`𝟙 ∈ C₁`, i.e. `H *ᵥ 𝟙 = 0`), for the
parity-check matrix `H` of eq. (10.76). -/
theorem one_mem_ofParityCheck_hammingParityCheck :
    (1 : Fin 7 → ZMod 2) ∈ LinearCode.ofParityCheck hammingParityCheck := by
  rw [LinearCode.mem_ofParityCheck_iff]
  decide

/-- **Every dual codeword `y ∈ C₂` has even weight**: `𝟙 · y = 0`. -/
theorem steaneDualCode_dotProduct_one {y : Fin 7 → ZMod 2} (hy : y ∈ steaneDualCode) :
    (1 : Fin 7 → ZMod 2) ⬝ᵥ y = 0 := by
  rw [steaneDualCode, LinearCode.mem_dual_iff] at hy
  exact hy 1 one_mem_ofParityCheck_hammingParityCheck

end AxQM.Concrete
