/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SquareRootMeasurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVMMap

/-!
# Coarse-graining the outcomes of a measurement

Given a measurement `m : Measurement ι S` and a function `g : ι → κ` on the outcome index, the
**coarse-grained measurement** `m.coarseGrain g : Measurement κ S` groups (merges) the original
outcomes according to `g`: measuring `m.coarseGrain g` and obtaining `k` has the summed Born
probability of all original outcomes lying over `k`.

## Main definitions / results

* `AxQM.Measurement.coarseGrain` — the coarse-grained measurement along `g : ι → κ`.
* `AxQM.Measurement.coarseGrain_bornProb` — its Born rule,
  `(m.coarseGrain g).bornProb ρ k = ∑_{i : g i = k} m.bornProb ρ i`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

namespace Measurement

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {S : QSystem}

/-- **Coarse-graining the outcomes of a measurement.** For a measurement `m : Measurement ι S` and a
function `g : ι → κ`, `m.coarseGrain g` is the measurement on `S` with outcome set `κ` that merges
the original outcomes along `g`.  It is the square-root measurement (`Measurement.ofPOVM`) of the
pushforward POVM `m.toPOVM.map g`, whose effect at `k` is the fibre-sum `∑_{i : g i = k} Eᵢ`
of `m`'s effects. -/
def coarseGrain (m : Measurement ι S) (g : ι → κ) : Measurement κ S :=
  Measurement.ofPOVM (m.toPOVM.map g)

/-- **Born rule of the coarse-grained measurement.** The probability that `m.coarseGrain g` assigns
to the merged outcome `k` on a state `ρ` is the sum of the probabilities `m` assigns to the
original outcomes lying over `k`: `(m.coarseGrain g).bornProb ρ k = ∑_{i : g i = k} m.bornProb ρ
i`. -/
theorem coarseGrain_bornProb (m : Measurement ι S) (g : ι → κ) (ρ : State S) (k : κ) :
    (m.coarseGrain g).bornProb ρ k =
      ∑ i ∈ Finset.univ.filter (fun i => g i = k), m.bornProb ρ i := by
  rw [coarseGrain, Measurement.ofPOVM_bornProb, POVM.map_toPMF]
  rfl

end Measurement

end AxQM
