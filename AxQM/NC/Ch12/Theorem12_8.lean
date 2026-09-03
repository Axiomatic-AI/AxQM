/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ArakiLiebEqualityConditions
import AxQM.Basic.API.Associator
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.EntropyMixLine
import AxQM.Basic.API.MeasurementCoarseGrain
import AxQM.Basic.API.MeasurementReindex
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.SquareRootMeasurement
import AxQM.Basic.API.Support
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.TensorPowState
import AxQM.Basic.API.TypicalSubspace
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.Basic.PiTensor
import AxQM.Core.ChannelHolevoChi
import AxQM.Core.HolevoChi
import AxQM.Core.ProductStateCapacity
import AxQM.Core.ProductStateCode
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch12.Problem12_1
import AxQM.NC.Ch2.Exercise2_78
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProductMap
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.ToMathlib.Analysis.SpecialFunctions.JointEntropy
import AxQM.ToMathlib.InformationTheory.TypicalSequence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The HSW theorem `χ(E) = C⁽¹⁾(E)` (N&C Theorem 12.8): converse steps + achievability assembly

*(N&C p. 555.)*

HSW theorem: chi(E) equals product-state capacity C^(1)(E).

* `channelHolevoChi_eq_productStateCapacity` — the HSW theorem itself, `χ(E) = C⁽¹⁾(E)`.
-/

open scoped BigOperators Topology

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The Holevo–Schumacher–Westmoreland (HSW) theorem** (Nielsen & Chuang, Theorem 12.8):  the
channel Holevo χ quantity of a memoryless quantum channel equals its product-state capacity,

`χ(E) = C⁽¹⁾(E)`.

The maximal rate of classical communication over `E` using product-state inputs (and joint
decoding measurements) is exactly the Holevo χ quantity `χ(E)` (N&C eq. (12.71)).

Needs `[Nonempty (State S)]` for the achievability direction (the encoder must name an input state);
the converse holds with no such hypothesis.
-/
theorem channelHolevoChi_eq_productStateCapacity [Nonempty (State S)] (E : State S → State S) :
    channelHolevoChi E = productStateCapacity E := sorry

end AxQM
