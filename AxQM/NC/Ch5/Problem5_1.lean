/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.PeriodShift
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.QuditPhaseGradient
import AxQM.Basic.API.QuditMeasurement
import AxQM.Basic.Measurement
import AxQM.Basic.API.SquareRootMeasurement
import AxQM.Basic.API.SameNonzeroSpectrum
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.Entropy
import AxQM.Basic.PartialTrace
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.Swap
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialIsometryOrthonormal
import AxQM.Basic.SystemIso
import AxQM.Basic.Composite
import AxQM.Core.QtowerHadamardLayer
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Core.QtowerControlQft
import AxQM.Core.QtowerMeasurement
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis
import AxQM.NC.Ch5.Exercise5_7

/-!
# Nielsen & Chuang, Problem 5.1 (a quantum circuit for the quantum Fourier transform)

*(N&C p. 243.)*

Construct a quantum circuit performing the QFT |j> -> (1/sqrt p) sum e^{2pi ijk/p}|k> for p prime.

* `bornProb_qtowerControlMeasurement_qftCircuit_nearestBin_prime_ge` — on the
  constructed circuit: measuring the `n+1` control wires of the *assembled* Kitaev circuit's output
  (Hadamard layer → controlled shift powers → inverse-QFT read-out, on `|0…0⟩ ⊗ F⁻¹|ℓ⟩`) in the
  computational basis, the best `(n+1)`-bit estimate is obtained with probability `≥ 4/π²` — a bound
  independent of register size.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Problem 5.1 — the constructed prime-`p` circuit reads out the best frequency
estimate** (the item's terminal finite-precision correctness, N&C §5.2.1). Running the whole
Kitaev circuit — the Hadamard layer, the controlled shift powers, and the inverse-QFT read-out —
on the computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, and then **measuring its `n+1` control wires in the
computational basis** (the terminal measurement of N&C Figure 5.2/5.3), the outcome is the
bit-string of the **nearest `(n+1)`-bit estimate** of the frequency `ℓ/p` with probability at
least `4/π²`: ``` 4/π² ≤ p(best (n+1)-bit estimate of ℓ/p). ``` The measured object is the
*constructed circuit's own output* — the full `qtowerControlInverseQft ∘ seqCtrlPow ∘
qtowerHadamardLayer` chain on `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, a state on `qtower (n+1) (qudit p)` — and the
measurement `Measurement.congr (qtowerSplitControl n (qudit p)).symm ((qtowerMeasurement
n).onLeft (qudit p))` is the joint computational-basis measurement of exactly the `n+1` control
wires (the target `qudit p` left untouched).

This is the sense in which the constructed circuit *performs* the QFT over `Z_p`: for prime `p`
no exact product-form circuit exists (5.4/Figure 5.1 need `N = 2ⁿ`), so `ℓ/p` is non-dyadic and
the read-out is a genuine finite-precision estimate — yet a constant fraction `4/π² ≈ 0.405` of
the probability, independent of register size, still concentrates on the best `(n+1)`-bit
estimate.
-/
theorem bornProb_qtowerControlMeasurement_qftCircuit_nearestBin_prime_ge
    (p : ℕ) [Fact p.Prime] (ℓ : Fin p) (n : ℕ) :
    4 / Real.pi ^ 2
      ≤ (Measurement.congr (qtowerSplitControl n (qudit p)).symm
            ((qtowerMeasurement n).onLeft (qudit p))).bornProb
          ((qtowerControlInverseQft n (qudit p)).evolvePure
              ((seqCtrlPow (periodShift p 1) (n + 1)).evolvePure
                ((qtowerHadamardLayer (n + 1)).evolvePure
                  (qtowerKet (n + 1) (fun _ => 0) (qftInverseFourierImage p ℓ))))).toState
          ((towerMeasurementOutcomeEquiv n).symm
            (nearestBin (2 * Real.pi * (ℓ : ℕ) / p) (2 ^ (n + 1)))) := sorry

end AxQM
