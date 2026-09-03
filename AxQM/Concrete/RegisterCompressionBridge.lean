/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubspaceCompression
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: compressing a wire-gate placement to the data register (matrix level)

A gate placed on a full register of `M` wires, split by an equivalence `Fin M ≃ Fin m ⊕ Fin n` into
`m` data wires and `n` ancilla wires held at `|1⟩`, is read on the data register alone along the
ancilla-`|1⟩` coordinate subspace.
-/

namespace AxQM.Concrete

open Matrix

variable {M m n D d : ℕ}

/-- **The register extension of a data bit-string.** Relative to a wire-splitting equivalence
`e : Fin M ≃ Fin m ⊕ Fin n`, `regExtend e x` is the full `M`-bit string carrying the data bits `x`
on the data wires (`Sum.inl`) and `1` on the ancilla wires (`Sum.inr`):
`regExtend e x k = Sum.elim x (fun _ => 1) (e k)`. It is the bit-string picture of holding the
ancilla wires at `|1⟩`. -/
def regExtend (e : Fin M ≃ Fin m ⊕ Fin n) (x : Fin m → Fin 2) : Fin M → Fin 2 :=
  fun k => Sum.elim x (fun _ => (1 : Fin 2)) (e k)

/-- **The data-into-full-register basis embedding.** `regEmbed fullEnc dataEnc e i` sends the data
basis index `i` to the full basis index of the extended bit-string `regExtend e (dataEnc.symm i)` —
the data bits of `i` on the data wires and `1` on the ancilla wires. It is the index map picking
out the ancilla-`|1⟩` coordinate subspace. -/
def regEmbed (fullEnc : (Fin M → Fin 2) ≃ Fin D) (dataEnc : (Fin m → Fin 2) ≃ Fin d)
    (e : Fin M ≃ Fin m ⊕ Fin n) : Fin d → Fin D :=
  fun i => fullEnc (regExtend e (dataEnc.symm i))

end AxQM.Concrete
