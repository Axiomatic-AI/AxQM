/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Problem10_1
import AxQM.Basic.API.CSSCode

/-!
# Nielsen & Chuang, Exercise 10.27 — the twisted CSS codes `CSSᵤ,ᵥ(C₁, C₂)`

*(N&C p. 452.)*

Codes CSS_{u,v}(C1,C2) defined by (10.75) are equivalent to CSS(C1,C2) in error-correcting
properties.

* `cssTwistUnitary`
* `cssCode`
* `cssTwistedCode`
* `cssTwistedCode_same_correction`
* `cssCode_same_correction`
-/

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **fixed local Pauli string** `W = Z^u X^v` relating a twisted CSS code to the standard one:
the composite of the phase-flip string `Z^u` (`phaseString u`) and the bit-flip string `X^v`
(`bitString v`), a single unitary `Evolution` of the register `bitReg ι` that does **not**
depend on the codeword. -/
def cssTwistUnitary (u v : ι → ZMod 2) : Evolution (bitReg ι) :=
  (phaseString u).comp (bitString v)

/-- The **standard CSS code** `CSS(C₁, C₂)` (Nielsen & Chuang, §10.4.2) as a set of code states: the
density operators `|x + C₂⟩⟨x + C₂|` of the standard coset states (eq. 10.64) over the cosets
`x ∈ C₁`. -/
def cssCode (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Set (State (bitReg ι)) :=
  (fun x => (cssStdState C₂ x).toState) '' (C₁ : Set (ι → ZMod 2))

/-- The **twisted CSS code** `CSSᵤ,ᵥ(C₁, C₂)` (Nielsen & Chuang, Exercise 10.27) as a set of code
states: the density operators `|x + C₂⟩ᵤ,ᵥ⟨x + C₂|ᵤ,ᵥ` of the twisted coset states (eq. 10.75) over
the cosets `x ∈ C₁`. -/
def cssTwistedCode (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Set (State (bitReg ι)) :=
  (fun x => (cssTwistedState C₂ u v x).toState) '' (C₁ : Set (ι → ZMod 2))

/-- **Same error-correcting properties, forward: a recovery for `CSS(C₁, C₂)` transfers to
`CSSᵤ,ᵥ(C₁, C₂)`** (Nielsen & Chuang, Exercise 10.27). If a recovery `R` corrects a noise
channel `E` on the standard code `CSS(C₁, C₂)`, then the conjugated recovery `W R W†` corrects
the conjugated channel `W E W†` on the twisted code `CSSᵤ,ᵥ(C₁, C₂)`, with the *same* fixed
local Pauli `W = Z^u X^v` (`cssTwistUnitary u v`) for every codeword.

Since `W` is a fixed local Pauli, `W E W†` is the same physical error model as `E` (Pauli
conjugation preserves error weight), so the twisted code corrects exactly the errors the standard
code does.
-/
theorem cssTwistedCode_same_correction (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι)
    [DecidablePred (· ∈ C₂)] {E R : State (bitReg ι) → State (bitReg ι)}
    (hR : Corrects R E (cssCode C₁ C₂)) :
    Corrects
      (fun σ => (cssTwistUnitary u v).evolve (R ((cssTwistUnitary u v).adjoint.evolve σ)))
      (fun ρ => (cssTwistUnitary u v).evolve (E ((cssTwistUnitary u v).adjoint.evolve ρ)))
      (cssTwistedCode u v C₁ C₂) := sorry

/-- **Same error-correcting properties, reverse: a recovery for `CSSᵤ,ᵥ(C₁, C₂)` transfers to
`CSS(C₁, C₂)`** (Nielsen & Chuang, Exercise 10.27).
-/
theorem cssCode_same_correction (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι)
    [DecidablePred (· ∈ C₂)] {E R : State (bitReg ι) → State (bitReg ι)}
    (hR : Corrects R E (cssTwistedCode u v C₁ C₂)) :
    Corrects
      (fun σ => (cssTwistUnitary u v).adjoint.evolve (R ((cssTwistUnitary u v).evolve σ)))
      (fun ρ => (cssTwistUnitary u v).adjoint.evolve (E ((cssTwistUnitary u v).evolve ρ)))
      (cssCode C₁ C₂) := sorry

end AxQM
