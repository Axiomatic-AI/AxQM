/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Key counts for public-key versus private-key cryptography

Consider a system of `n` users, *any* pair of which wishes to be able to communicate
privately.  This file counts the cryptographic keys that must be distributed under the two
classical paradigms, formalising Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Exercise 12.25 (p. 584).
-/

@[expose] public section

namespace Cryptography.KeyDistribution

variable (V : Type*) [Fintype V]

/-- The public keys distributed among a set `V` of users under **public-key** cryptography:
one published public key per user.  (The private half of each key pair never leaves its
owner and so is not distributed.) -/
def publicKeys : Finset V := Finset.univ

/-- **Public-key count.** A public-key system for `n` users distributes `n` keys, one per
user. -/
theorem card_publicKeys : (publicKeys V).card = Fintype.card V := sorry

variable [DecidableEq V]

/-- The secret keys distributed among a set `V` of users under **private-key** cryptography:
one shared key per unordered pair of *distinct* users that wishes to communicate, i.e. one
per edge of the complete graph `⊤` on `V`. -/
noncomputable def privateKeys : Finset (Sym2 V) := (⊤ : SimpleGraph V).edgeFinset

/-- **Private-key count** (closed form).  A private-key system for `n` users distributes
`n * (n - 1) / 2` keys, one per pair of users. -/
theorem card_privateKeys : (privateKeys V).card = Fintype.card V * (Fintype.card V - 1) / 2 := sorry

end Cryptography.KeyDistribution
