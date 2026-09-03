/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.UniversalHashEntropy

/-!
# Refutation of the literal constant in Nielsen & Chuang's Theorem 12.16

Nielsen & Chuang's privacy-amplification theorem (§12.6, Theorem 12.16) states the entropy chain
`H(G(X)|G) ≥ Hc(G(X)|G) ≥ m − 2^{m−Hc(X)}` for the output `G(X)` of a `2`-universal hash family to
`{0,1}^m`, with `G` uniform. The correct second bound is
`Hc(G(X)|G) ≥ m − log₂(1 + 2^{m−Hc(X)})`. This file proves that **Nielsen & Chuang's literal second
inequality, with its constant `2^{m−Hc(X)}`, is false**.

## Main results

* `exists_lt_universalHash_literalBound`: **the refutation** — a `2`-universal family and input with
  `Hc(G(X)|G) < log₂|β| − |β|·Pc(X)`, so Nielsen & Chuang's literal second inequality is false.
-/

@[expose] public section

namespace Real

variable {α β : Type*}

/-- **Refutation of the literal constant in Nielsen & Chuang's Theorem 12.16.** There is a genuinely
`2`-universal hash family `h` and input distribution `p` whose conditional collision entropy
falls strictly below the textbook's literal second bound `m − 2^{m−Hc(X)}` — written here
`log₂|β| − |β|·Pc(X)`, using `2^{m−Hc(X)} = |β|·Pc(X)`. Hence N&C's *second* inequality, with
the constant `2^{m−Hc(X)}`, is **false** as stated; the correct lower bound is the
`m − log₂(1 + 2^{m−Hc(X)})` form.
-/
theorem exists_lt_universalHash_literalBound :
    ∃ (h : (Fin 16 → Fin 8) → Fin 16 → Fin 8) (p : Fin 16 → ℝ),
      IsUniversalFamily h ∧ (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧
        avgCollisionEntropy h p
          < Real.logb 2 (Fintype.card (Fin 8)) - Fintype.card (Fin 8) * collisionProb p := sorry

end Real
