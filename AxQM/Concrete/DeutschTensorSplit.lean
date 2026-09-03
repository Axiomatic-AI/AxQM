/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import AxQM.Concrete.DeutschRegisterBridge

/-!
# Concrete: the leading-three-wires gate factors as `C²(g) ⊗ₖ 1` (matrix level, N&C Ex 4.44)

## The construction and results

* `regTensorEnc e restEnc : (Fin M → Fin 2) ≃ Fin (8 · r)` — the split encoding: leading three
  wires via `finThreeRegEnc`, remaining `n` wires via `restEnc`, packed with `finProdFinEquiv`.
-/

namespace AxQM.Concrete

open Matrix

variable {M n r : ℕ}

/-- **The register tensor-split encoding.** For a wire-splitting equivalence
`e : Fin M ≃ Fin 3 ⊕ Fin n` and a `rest`-register encoding `restEnc : (Fin n → Fin 2) ≃ Fin r`,
`regTensorEnc e restEnc : (Fin M → Fin 2) ≃ Fin (8 · r)` reads a bit-string by packing its leading
three wires (`e ⁻¹ (inl ·)`) into `Fin 8` via the canonical three-wire encoding `finThreeRegEnc` and
its remaining wires (`e ⁻¹ (inr ·)`) into `Fin r` via `restEnc`, then packing the pair
`Fin 8 × Fin r` into the flat index `Fin (8 · r)` along `finProdFinEquiv`. This is the encoding
against which the leading-three-wires doubly-controlled gate factors as `C²(g) ⊗ₖ 1`. -/
def regTensorEnc (e : Fin M ≃ Fin 3 ⊕ Fin n) (restEnc : (Fin n → Fin 2) ≃ Fin r) :
    (Fin M → Fin 2) ≃ Fin (8 * r) :=
  (Equiv.arrowCongr e (Equiv.refl (Fin 2))).trans
    ((Equiv.sumArrowEquivProdArrow (Fin 3) (Fin n) (Fin 2)).trans
      ((Equiv.prodCongr finThreeRegEnc restEnc).trans finProdFinEquiv))

end AxQM.Concrete
