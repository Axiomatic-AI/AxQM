/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChiPureCard

/-!
# N&C Exercise 12.11 — the HSW χ maximum is achieved by `≤ d²` pure-state ensembles

*(N&C p. 555.)*

Show max in HSW chi expression achieved by ensemble of <=d^2 pure states.

* `channelHolevoChi_eq_sSup_pureEnsemble`
* `channelHolevoChi_eq_sSup_pureLeCardEnsemble`
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang Exercise 12.11, Part 1** (the HSW χ maximum is achieved by pure-state
ensembles): for a channel `E`, the Holevo χ quantity `χ(E)` — the maximum in eq. (12.71) over
*all* input ensembles — equals the supremum of the output Holevo χ over **pure-state** input
ensembles alone,

`χ(E) = sSup (channelHolevoChiPureSet E)`.
-/
theorem channelHolevoChi_eq_sSup_pureEnsemble {E : State S → State S} (hE : IsChannel E) :
    channelHolevoChi E = sSup (channelHolevoChiPureSet E) := sorry

/-- **Nielsen & Chuang Exercise 12.11, Part 2** (the HSW χ maximum is achieved by an ensemble of `≤
d²` pure states): for a channel `E`, the Holevo χ quantity `χ(E)` — the maximum in eq. (12.71)
over *all* input ensembles — equals the supremum of the output Holevo χ over **pure-state**
input ensembles of at most `d² = S.dim ^ 2` elements, where `d` is the dimension of the channel
input:

`χ(E) = sSup (channelHolevoChiPureLeCardSet E)`.
-/
theorem channelHolevoChi_eq_sSup_pureLeCardEnsemble {E : State S → State S} (hE : IsChannel E) :
    channelHolevoChi E = sSup (channelHolevoChiPureLeCardSet E) := sorry

end AxQM
