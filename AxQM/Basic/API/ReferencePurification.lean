/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.Basic.SystemIso
import AxQM.Basic.API.SystemIsoComm
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.PureMarginalEntropy

/-!
# Reference purification with the reference on the left (N&C §12.4.1)

Nielsen & Chuang's discussion of entropy exchange and coherent information (§12.4.1–12.4.2)
introduces a *reference system* `R` and a purification `|RQ⟩` of the input state `ρ` on `Q`,
written with the reference `R` as the **first** factor so that a quantum operation `E` on `Q`
acts on the *right* factor of `R ⊗ Q`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Reference purification with the reference on the left.** For a state `ρ` on `S`, this is the
canonical purification `ρ.purify` (a pure state on `S ⊗ R` with left marginal `ρ`) with its two
factors swapped, giving a pure state on `R ⊗ S` — the reference `R` first, the system `S` second.
Nielsen & Chuang §12.4.1 use exactly this ordering `|RQ⟩` so that a quantum operation on the system
acts on the right factor. -/
def State.refPurify (ρ : State S) :
    PureState ((QSystem.ofModel (EuclideanSpace ℂ (Fin S.dim))).compose S) :=
  PureState.congr (QSystem.Iso.comm S _) ρ.purify

end AxQM
