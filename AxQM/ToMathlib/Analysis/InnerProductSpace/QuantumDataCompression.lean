/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition
public import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProductMap

/-! # Quantum data compression: schemes, entanglement fidelity, and reliability

This file sets up the operational framework for Schumacher's quantum noiseless channel coding
theorem (Nielsen–Chuang, *Quantum Computation and Quantum Information*, §12.2.2): the notion of a
**rate-`R` quantum compression scheme** for an i.i.d. quantum source `{H, ρ}`, the **entanglement
fidelity** through such a scheme, and the resulting **reliability** predicate.

## Main definitions and results

* `ContinuousLinearMap.QuantumCompressionScheme` — a rate-`numBits` compression scheme on `K`.
* `ContinuousLinearMap.QuantumCompressionScheme.composite` — the operation elements `Dₖ Cⱼ` of
  `Dₙ ∘ Cₙ`.
* `ContinuousLinearMap.QuantumCompressionScheme.fidelity` — `F(ρ, Dₙ ∘ Cₙ)`, the entanglement
  fidelity of the source `ρ` through the scheme.
* `ContinuousLinearMap.ReliablyCompressible` — a source `ρ` is reliably compressible at rate `R`:
  a family of rate-`R` schemes exists whose entanglement fidelity for `ρ^⊗n` tends to `1`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.50)–(12.58)).
-/

open scoped InnerProductSpace TensorProduct

@[expose] public section

namespace ContinuousLinearMap

/-- A **rate-`numBits` quantum compression scheme** on a Hilbert space `K` (Nielsen & Chuang,
§12.2.2), standing for one block length `n` with `K = H^⊗n` and `numBits = ⌊nR⌋`. It bundles a
compression operation `Cₙ` and a decompression operation `Dₙ`, given by their Kraus families, with
the requirement that `Cₙ` compresses into a subspace of dimension at most `2^numBits`.

Both operations are quantum operations *on `K`* (endomorphisms), and the compressed space is the
range of an orthogonal projector `compressedProjection = S(n)` of dimension `≤ 2^numBits` through
which every compression element factors (Eq. (12.55), `Cⱼ = S(n) Cⱼ`). -/
structure QuantumCompressionScheme (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] [CompleteSpace K] (numBits : ℕ) where
  /-- The number of Kraus operators of the compression operation `Cₙ`. -/
  encCard : ℕ
  /-- The number of Kraus operators of the decompression operation `Dₙ`. -/
  decCard : ℕ
  /-- The Kraus operators (operation elements) `Cⱼ` of the compression operation `Cₙ`. -/
  encode : Fin encCard → K →L[ℂ] K
  /-- The Kraus operators (operation elements) `Dₖ` of the decompression operation `Dₙ`. -/
  decode : Fin decCard → K →L[ℂ] K
  /-- `Cₙ` is trace-preserving: `∑ⱼ Cⱼ† Cⱼ = 1`. -/
  encode_isTracePreserving : ∑ j, adjoint (encode j) * encode j = 1
  /-- `Dₙ` is trace-preserving: `∑ₖ Dₖ† Dₖ = 1`. -/
  decode_isTracePreserving : ∑ k, adjoint (decode k) * decode k = 1
  /-- The projector `S(n)` onto the compressed subspace (the `2^numBits`-dimensional space). -/
  compressedProjection : K →L[ℂ] K
  /-- `S(n)` is an orthogonal (self-adjoint idempotent) projection. -/
  isStarProjection_compressedProjection : IsStarProjection compressedProjection
  /-- Every compression element maps into the compressed subspace: `Cⱼ = S(n) Cⱼ`. -/
  compressedProjection_mul_encode : ∀ j, compressedProjection * encode j = encode j
  /-- Rate bound: the compressed subspace has dimension at most `2^numBits`. -/
  finrank_range_compressedProjection_le :
    Module.finrank ℂ (LinearMap.range (compressedProjection : K →ₗ[ℂ] K)) ≤ 2 ^ numBits

namespace QuantumCompressionScheme

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [CompleteSpace K] {numBits : ℕ}

/-- The operation elements of the combined compression–decompression operation `Dₙ ∘ Cₙ`: the
products `Dₖ Cⱼ`, indexed by pairs `(k, j)`. -/
def composite (sch : QuantumCompressionScheme K numBits) :
    Fin sch.decCard × Fin sch.encCard → K →L[ℂ] K :=
  fun p => sch.decode p.1 * sch.encode p.2

/-- The **entanglement fidelity** `F(ρ, Dₙ ∘ Cₙ)` of a source `ρ` through the scheme, i.e. the
entanglement fidelity of `ρ` under the combined operation `Dₙ ∘ Cₙ` (Nielsen & Chuang, §12.2.2). -/
noncomputable def fidelity (sch : QuantumCompressionScheme K numBits) (ρ : K →L[ℂ] K) : ℝ :=
  ContinuousLinearMap.entanglementFidelity ρ sch.composite

end QuantumCompressionScheme

/- Only `[FiniteDimensional ℂ H]` is required below: the schemes live on the block spaces `H^⊗n`,
for which `CompleteSpace` is derived. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A source `ρ` (a density operator on `H`) is **reliably compressible at rate `R`** if there is a
family of rate-`R` quantum compression schemes — one for each block length `n`, on the block space
`H^⊗n` with qubit budget `⌊nR⌋` — whose entanglement fidelity for the source `ρ^⊗n` tends to `1` as
`n → ∞` (Nielsen & Chuang, §12.2.2). Here `ρ^⊗n = PiTensorProduct.mapCLM (fun _ ↦ ρ)` is the
`n`-fold tensor power of `ρ`. -/
def ReliablyCompressible (ρ : H →L[ℂ] H) (R : ℝ) : Prop :=
  ∃ sch : (n : ℕ) → QuantumCompressionScheme (⨂[ℂ] (_ : Fin n), H) ⌊(n : ℝ) * R⌋₊,
    Filter.Tendsto
      (fun n => (sch n).fidelity (PiTensorProduct.mapCLM fun _ : Fin n => ρ))
      Filter.atTop (nhds 1)

end ContinuousLinearMap
