/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.MeasurementPrecompose
import AxQM.Basic.Measurement
import AxQM.Basic.Evolution
import AxQM.Basic.API.DeferredMeasurementReindex
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.AdaptiveMeasurement
import AxQM.Basic.API.MeasurementReindex
import AxQM.Basic.Composite

/-!
# Finite-round two-way LOCC protocols on a bipartite system

A formal type of **LOCC protocol** (Local Operations and Classical Communication) over a bipartite
system `A ⊗ B`, its deterministic transformation semantics, and the one-way (single
Alice-measurement / Bob-unitary) protocol form, as needed to state **Nielsen & Chuang,
Proposition 12.14**.
-/

noncomputable section

namespace AxQM

/-- A **finite-round two-way LOCC protocol** on the bipartite system `A ⊗ B`: a tree of local
operations (measurements and unitaries by either party) interleaved with classical communication.
At an `aliceMeasure`/`bobMeasure` node the measuring party broadcasts its `Fin n` outcome and the
continuation `k` may depend on it (the classical record); `aliceUnitary`/`bobUnitary` are
deterministic local unitary rounds. Outcome sets are `Fin n` (every finite measurement reindexes to
this). -/
inductive LOCCProtocol (A B : QSystem) where
  /-- Stop: the protocol performs no further operations. -/
  | terminal : LOCCProtocol A B
  /-- Alice measures the `n`-outcome measurement `m` on her factor `A`, broadcasts the outcome `j`,
  and the protocol continues as `k j` (Alice→Bob classical communication). -/
  | aliceMeasure (n : ℕ) (m : Measurement (Fin n) A) (k : Fin n → LOCCProtocol A B) :
      LOCCProtocol A B
  /-- Bob measures the `n`-outcome measurement `m` on his factor `B`, broadcasts the outcome `j`,
  and the protocol continues as `k j` (Bob→Alice classical communication). -/
  | bobMeasure (n : ℕ) (m : Measurement (Fin n) B) (k : Fin n → LOCCProtocol A B) :
      LOCCProtocol A B
  /-- Alice applies the local unitary `U` on her factor `A`, then continues as `k`. -/
  | aliceUnitary (U : Evolution A) (k : LOCCProtocol A B) : LOCCProtocol A B
  /-- Bob applies the local unitary `V` on his factor `B`, then continues as `k`. -/
  | bobUnitary (V : Evolution B) (k : LOCCProtocol A B) : LOCCProtocol A B

variable {A B : QSystem}

/-- **Deterministic transformation semantics.** `P.Transforms ρ σ` holds when running the protocol
`P` on the joint state `ρ` sends *every* branch of nonzero probability to `σ`. This is N&C's
"transformed to `σ` by LOCC" in the deterministic sense: the outcome is `σ` regardless of the
measurement results. -/
def LOCCProtocol.Transforms :
    LOCCProtocol A B → State (A.compose B) → State (A.compose B) → Prop
  | .terminal, ρ, σ => ρ = σ
  | .aliceMeasure _ m k, ρ, σ =>
      ∀ j, (h : (m.onLeft B).bornProb ρ j ≠ 0) →
        (k j).Transforms ((m.onLeft B).postMeasurement ρ j h) σ
  | .bobMeasure _ m k, ρ, σ =>
      ∀ j, (h : (m.onRight A).bornProb ρ j ≠ 0) →
        (k j).Transforms ((m.onRight A).postMeasurement ρ j h) σ
  | .aliceUnitary U k, ρ, σ => k.Transforms ((U.onLeft B).evolve ρ) σ
  | .bobUnitary V k, ρ, σ => k.Transforms ((V.onRight A).evolve ρ) σ

/-- The canonical **one-way protocol** of N&C Proposition 12.14: Alice performs the single
measurement `m` on her factor, broadcasts the outcome `j`, and Bob applies the conditional unitary
`V j` on his factor. -/
def LOCCProtocol.oneWay (n : ℕ) (m : Measurement (Fin n) A) (V : Fin n → Evolution B) :
    LOCCProtocol A B :=
  .aliceMeasure n m (fun j => .bobUnitary (V j) .terminal)

/-- **One-way LOCC reachability** of joint states (N&C Proposition 12.14's target form): there is an
Alice measurement `{Mⱼ}` and a family of Bob unitaries `{Vⱼ}` such that, deterministically on
every branch, Alice measuring and Bob applying `Vⱼ` carries `ρ` to `σ`. -/
def OneWayLOCC (ρ σ : State (A.compose B)) : Prop :=
  ∃ (n : ℕ) (m : Measurement (Fin n) A) (V : Fin n → Evolution B),
    (LOCCProtocol.oneWay n m V).Transforms ρ σ

end AxQM
