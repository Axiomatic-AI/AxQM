/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: tensor powers of the plus state (Nielsen & Chuang, Exercise 2.26)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.26 (p. 74)
asks: for `|ψ⟩ = (|0⟩ + |1⟩)/√2`, write out `|ψ⟩^⊗2` and `|ψ⟩^⊗3` explicitly, **both**
in terms of tensor products like `|0⟩|1⟩` and **using the Kronecker product**.

## Contents

* `vecKron` — the vector Kronecker product.
* `vecKron_xPlus_xPlus` — the Kronecker-product form of `|ψ⟩^⊗2`: the explicit
  4-component column vector with every entry `1/2`, i.e. `½(1, 1, 1, 1)ᵀ`.
* `vecKron_xPlus_xPlus_eq_sum` — the tensor-product form of `|ψ⟩^⊗2`:
  `½(|00⟩ + |01⟩ + |10⟩ + |11⟩)`.
* `vecKron_xPlus_vecKron_xPlus_xPlus` — the Kronecker-product form of `|ψ⟩^⊗3`: the
  explicit 8-component column vector with every entry `1/(2√2) = (1/√2)/2`.
* `vecKron_xPlus_vecKron_xPlus_xPlus_eq_sum` — the tensor-product form of `|ψ⟩^⊗3`:
  `1/(2√2) · (|000⟩ + |001⟩ + ⋯ + |111⟩)`, all eight computational-basis kets.
-/

namespace AxQM.Concrete

open Matrix

/-- The Kronecker (tensor) product of two finite complex column vectors, indexed by the product
index type: `(u ⊗ v) (i, j) = uᵢ · vⱼ`. The tensor-product basis ket `|i⟩|j⟩` is `vecKron (ket
i) (ket j)`. -/
def vecKron {m n : Type*} (u : m → ℂ) (v : n → ℂ) : m × n → ℂ := fun p => u p.1 * v p.2

/-- **`|ψ⟩^⊗2` via the Kronecker product.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`, the Kronecker
product `|ψ⟩ ⊗ |ψ⟩` is the explicit 4-component column vector with every entry `1/2`:
`|ψ⟩^⊗2 = ½(1, 1, 1, 1)ᵀ`. -/
theorem vecKron_xPlus_xPlus : vecKron xPlus xPlus = fun _ => (1 / 2 : ℂ) := sorry

/-- **`|ψ⟩^⊗2` in terms of tensor products.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`,
`|ψ⟩^⊗2 = ½(|00⟩ + |01⟩ + |10⟩ + |11⟩)`, where `|ij⟩ = vecKron (ket i) (ket j)`. -/
theorem vecKron_xPlus_xPlus_eq_sum :
    vecKron xPlus xPlus =
      (1 / 2 : ℂ) • (vecKron (ket 0) (ket 0) + vecKron (ket 0) (ket 1) +
        vecKron (ket 1) (ket 0) + vecKron (ket 1) (ket 1)) := sorry

/-- **`|ψ⟩^⊗3` via the Kronecker product.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`, the Kronecker
product `|ψ⟩ ⊗ (|ψ⟩ ⊗ |ψ⟩)` is the explicit 8-component column vector with every entry
`1/(2√2) = (1/√2)/2`. -/
theorem vecKron_xPlus_vecKron_xPlus_xPlus :
    vecKron xPlus (vecKron xPlus xPlus) = fun _ => invSqrt2 / 2 := sorry

/-- **`|ψ⟩^⊗3` in terms of tensor products.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`,
`|ψ⟩^⊗3 = 1/(2√2) · (|000⟩ + |001⟩ + |010⟩ + |011⟩ + |100⟩ + |101⟩ + |110⟩ + |111⟩)`,
the equal superposition of all eight computational-basis kets
`|ijk⟩ = vecKron (ket i) (vecKron (ket j) (ket k))`. -/
theorem vecKron_xPlus_vecKron_xPlus_xPlus_eq_sum :
    vecKron xPlus (vecKron xPlus xPlus) =
      (invSqrt2 / 2) • (vecKron (ket 0) (vecKron (ket 0) (ket 0)) +
        vecKron (ket 0) (vecKron (ket 0) (ket 1)) +
        vecKron (ket 0) (vecKron (ket 1) (ket 0)) +
        vecKron (ket 0) (vecKron (ket 1) (ket 1)) +
        vecKron (ket 1) (vecKron (ket 0) (ket 0)) +
        vecKron (ket 1) (vecKron (ket 0) (ket 1)) +
        vecKron (ket 1) (vecKron (ket 1) (ket 0)) +
        vecKron (ket 1) (vecKron (ket 1) (ket 1))) := sorry

end AxQM.Concrete
