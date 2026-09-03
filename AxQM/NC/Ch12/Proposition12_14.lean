/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.Swap
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.Composite
import AxQM.Basic.API.SameNonzeroSpectrum
import AxQM.Basic.API.Entropy
import AxQM.Basic.PartialTrace
import AxQM.Basic.Measurement
import AxQM.Basic.API.SquareRootMeasurement
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialIsometryOrthonormal
import Mathlib.Analysis.InnerProductSpace.SingularValues
import AxQM.NC.Ch2.Exercise2_80
import AxQM.Core.LOCCProtocol

/-!
# Nielsen & Chuang, Proposition 12.14 (LOCC reduction)

*(N&C p. 575.)*

LOCC transform reducible to Alice-measure, send j, Bob-unitary protocol.

* `of_transforms_pureState`
* `of_exists_transforms_pureState`
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap (adjoint)
open InnerProductSpace (crossSynthesis)

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {C : QSystem}

variable {S T : QSystem}

variable {A B : QSystem}

/-- **Proposition 12.14 (the reduction).** Every finite-round two-way LOCC protocol `P` that
deterministically transforms a bipartite **pure** state `ψ` into `σ` — i.e. every
nonzero-probability branch of `P` on `ψ` ends in `σ` (`LOCCProtocol.Transforms`) — can be replaced
by a **single-round one-way** protocol: Alice performs one measurement `{Mⱼ}`, sends the outcome `j`
to Bob, who applies a conditional unitary `Vⱼ` (`OneWayLOCC ψ.toState σ`).

The target `σ` is left an arbitrary `State`, generalising N&C's pure `|ϕ⟩`.
-/
theorem OneWayLOCC.of_transforms_pureState :
    ∀ (P : LOCCProtocol A B) (ψ : PureState (A ⊗ B)) (σ : State (A ⊗ B)),
      P.Transforms ψ.toState σ → OneWayLOCC ψ.toState σ := sorry

/-- **Proposition 12.14, N&C's phrasing.** If a bipartite pure state `ψ` *can be transformed* to `σ`
by some finite-round two-way LOCC protocol (`∃ P, P.Transforms ψ.toState σ`), then the
transformation is achievable by a one-way protocol — Alice measures once, sends the outcome to
Bob, who applies a conditional unitary (`OneWayLOCC ψ.toState σ`). -/
theorem OneWayLOCC.of_exists_transforms_pureState (ψ : PureState (A ⊗ B)) (σ : State (A ⊗ B))
    (h : ∃ P : LOCCProtocol A B, P.Transforms ψ.toState σ) : OneWayLOCC ψ.toState σ := sorry

end AxQM
