/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import AxQM.ToMathlib.Analysis.Fourier.ZModUnitary

/-! # Subspace fidelity controls the entanglement fidelity (Nielsen & Chuang, Problem 9.3)

**Fact (5)** of Nielsen & Chuang §9.3 — the content of *Problem 9.3*: if a
trace-preserving quantum operation preserves every pure state in the support of a density operator
`ρ` to fidelity at least `1 − η`, then it preserves `ρ`'s entanglement to fidelity at least
`1 − 3η/2`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §9.3 (Problem 9.3, fact (5)).
-/

open scoped InnerProductSpace ComplexConjugate

open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

omit [DecidableEq ι] in
/-- **Fact (5) of Nielsen & Chuang §9.3 (Problem 9.3).** Let `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` be a density
operator written in a spectral eigenbasis (`b` an orthonormal basis, `p` a probability vector),
and let `E` be a trace-preserving quantum operation (operation elements `Eⱼ`, `Σⱼ Eⱼ† Eⱼ = 1`). If
`E` preserves every pure state in the support of `ρ` to fidelity at least `1 − η`, then it
preserves `ρ`'s entanglement to fidelity at least `1 − 3η/2`. -/
theorem entanglementFidelity_ge_one_sub_of_subspace_fidelity (b : OrthonormalBasis ι ℂ H)
    (p : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) {η : ℝ}
    (hfid : ∀ ψ : H, ‖ψ‖ = 1 → (∀ a, p a = 0 → inner ℂ (b a) ψ = 0) →
      1 - η ≤ RCLike.re (inner ℂ ψ (krausSumₗ E (rankOne ℂ ψ ψ) ψ))) :
    1 - 3 * η / 2 ≤ entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (b a) (b a)) E := sorry

end ContinuousLinearMap
