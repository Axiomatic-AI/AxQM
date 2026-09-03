/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Proposition12_18
import AxQM.Basic.API.BB84

/-!
# Nielsen & Chuang, Exercise 12.38 (distinguishing non-orthogonal states breaks QKD)

*(N&C p. 602.)*

Show ability to distinguish non-orthogonal states would break BB84 and QKD.

* `StateDistinguisher`
* `intercept`
* `intercept_signal` — the forwarded state *equals* the transmitted one, so the attack is
  undetectable: Bob's statistics, and the check-bit comparison meant to catch an eavesdropper, are
  unchanged.
* `intercept_reveals` — the read-out recovers the full label, so the attack is informative: Eve
  learns which signal was sent.
* `bb84Signal`
* `bb84_distinguisher_compromises_security` — the two together at Alice's four signals: Eve learns
  her data bit `a` *and* Bob receives the identical `bb84State a b`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A : QSystem}

/-! ### The attack: distinguishing non-orthogonal states breaks BB84

Exercise 12.38 asks for the **forward** direction: *were* the (physically unavailable) ability to
distinguish non-orthogonal states nevertheless in hand, it would break the protocol. That ability
is modelled abstractly as a classical read-out `identify` correctly labelling each transmitted
signal, generic in the signal family `signal : ι → PureState S`. -/

variable {ι : Type*} {S : QSystem} {signal : ι → PureState S}

/-- **The hypothesised ability to distinguish the transmitted states (Exercise 12.38).** A
device that, presented with a transmitted signal `signal i`, returns its classical label `i` —
the counterfactual "ability to distinguish non-orthogonal states". The read-out alone captures
the ability: knowing the classical label, an eavesdropper can re-prepare the identified state
and forward it. Physically no such device exists for non-orthogonal signals; the content of the
exercise is what it *would* enable. -/
structure StateDistinguisher (signal : ι → PureState S) where
  /-- Eve's classical read-out of which signal state was transmitted. -/
  identify : PureState S → ι
  /-- The read-out is correct: it recovers the label of every transmitted signal state. -/
  identify_signal : ∀ i, identify (signal i) = i

/-- **Eve's intercept–resend attack (Exercise 12.38).** Using the distinguisher `D`, Eve reads
the classical label of the intercepted signal and re-prepares — hence forwards to Bob — the
identified state `signal (D.identify ψ)`. -/
def StateDistinguisher.intercept (D : StateDistinguisher signal) (ψ : PureState S) : PureState S :=
  signal (D.identify ψ)

/-- **The intercept–resend attack is undetectable (Exercise 12.38).** Bob receives *exactly* the
state Alice sent, `D.intercept (signal i) = signal i`. Because the forwarded state is identical
to the original, Bob's measurement statistics — and hence the check-bit comparison that would
reveal an eavesdropper — are unchanged. -/
theorem StateDistinguisher.intercept_signal (D : StateDistinguisher signal) (i : ι) :
    D.intercept (signal i) = signal i := sorry

/-- **The intercept–resend attack reveals the transmitted label (Exercise 12.38).** Eve's
read-out recovers the full classical label `i` of the transmitted signal — for BB84 this is
Alice's `(data, basis)` pair, so Eve learns the raw key bit. -/
theorem StateDistinguisher.intercept_reveals (D : StateDistinguisher signal) (i : ι) :
    D.identify (signal i) = i := sorry

/-- **The BB84 signal family** as a map of Alice's `(data, basis)` bits to her encoding state,
`bb84Signal (a, b) = bb84State a b` (N&C eqs. 12.180–12.183). -/
def bb84Signal (p : Fin 2 × Fin 2) : PureState qubit := bb84State p.1 p.2

/-- **The ability to distinguish non-orthogonal states compromises BB84 (Exercise 12.38).** Given
the hypothesised distinguisher `D`, for every choice `(a, b)` of Alice's data and basis bits Eve
simultaneously (i) learns Alice's data bit `a` and (ii) forwards to Bob the *identical* state
`bb84State a b`, introducing no detectable disturbance. An eavesdropper wielding the ability to
distinguish non-orthogonal states therefore reads Alice's raw key while passing the check-bit
test — the security of BB84 is compromised. -/
theorem bb84_distinguisher_compromises_security
    (D : StateDistinguisher bb84Signal) (a b : Fin 2) :
    (D.identify (bb84State a b)).1 = a ∧ D.intercept (bb84State a b) = bb84State a b := sorry

end AxQM
