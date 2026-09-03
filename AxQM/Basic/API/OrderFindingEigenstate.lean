/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qudit
import AxQM.Concrete.OrderFindingOrbit
import AxQM.ToMathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# AxQM.Basic.API — the order-finding eigenstates `|u_s⟩` and their reconstruction

The development behind **Nielsen & Chuang Exercise 5.13**. In the order-finding
subroutine (§5.3.1) one fixes a modulus `N` and a residue `x` coprime to `N` (a unit of `ZMod N`) of
multiplicative order `r`, and the unitary `U|y⟩ = |xy mod N⟩`.

## Main declarations
* `orderEigenstate x s` — the eigenstate `|u_s⟩` as a genuine `PureState (qudit N)`; its
  normalization is the Pythagorean identity `‖(1/√r) ∑_k e^{−2πisk/r}|x^k⟩‖² = (1/r)·r = 1` over the
  orthonormal orbit family (`Orthonormal.norm_sum_smul_sq`).
* `orderEigenstate_reconstruct` — **eq. (5.45)** for every `k : ℕ`, the inverse-DFT reconstruction.
* `orderEigenstate_sum_eq_one` — **eq. (5.44)**, the `k = 0` specialisation (`|x^0 mod N⟩ = |1⟩`).
-/

noncomputable section

namespace AxQM

open scoped Matrix
open AxQM.Concrete (orbitIndex orbitIndex_fin_injective orbitIndex_mod)

/-- The complex-exponential DFT phase `e^{−2πi ab/r}` has unit modulus (it is `e^{iθ}` for a real
angle `θ`). -/
private theorem norm_exp_dft (a b r : ℕ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) * (b : ℂ)) / (r : ℂ)))‖ = 1 := by
  rw [show (-(2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) * (b : ℂ)) / (r : ℂ)))
        = ((-(2 * Real.pi * ((a : ℝ) * (b : ℝ)) / (r : ℝ)) : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- **The order-finding eigenstate** `|u_s⟩ = (1/√r) ∑_{k<r} e^{−2πisk/r} |x^k mod N⟩` of N&C eq.
(5.37), for a unit `x` of `ZMod N` of order `r = orderOf x` and label `s : Fin r`, as a
`PureState` of `qudit N`. -/
def orderEigenstate {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (s : Fin (orderOf x)) :
    PureState (qudit N) where
  vec := ∑ k : Fin (orderOf x),
    ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ))))
      • (quditBasis (orbitIndex x (k : ℕ))).vec
  normalized := by
    have hr : 0 < orderOf x := orderOf_pos x
    have horth : Orthonormal ℂ (fun k : Fin (orderOf x) =>
        (quditBasis (orbitIndex x (k : ℕ))).vec) :=
      (quditBasis_orthonormal N).comp _ (orbitIndex_fin_injective x)
    have hcoeff : ∀ k : Fin (orderOf x),
        ‖(Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) /
            (orderOf x : ℂ)))‖ ^ 2 = (orderOf x : ℝ)⁻¹ := by
      intro k
      rw [norm_mul, norm_exp_dft, mul_one, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
    have hsq : ‖(∑ k : Fin (orderOf x),
        ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) /
            (orderOf x : ℂ)))) • (quditBasis (orbitIndex x (k : ℕ))).vec)‖ ^ 2 = 1 := by
      rw [horth.norm_sum_smul_sq, Finset.sum_congr rfl (fun k _ => hcoeff k)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ (by exact_mod_cast hr.ne')]
    rw [← Real.sqrt_one, ← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- **Nielsen & Chuang, Exercise 5.13, eq. (5.45).** The order-finding eigenstates reconstruct the
orbit basis states by the inverse discrete Fourier transform: for every `k : ℕ`,

`(1/√r) ∑_{s<r} e^{2πisk/r} |u_s⟩ = |x^k mod N⟩`.
-/
theorem orderEigenstate_reconstruct {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (k : ℕ) :
    ∑ s : Fin (orderOf x),
        ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ)))
        • (orderEigenstate x s).vec
      = (quditBasis (orbitIndex x k)).vec := sorry

/-- **Nielsen & Chuang, Exercise 5.13, eq. (5.44).** The equal-weight superposition of all order-
finding eigenstates is the trivially preparable computational basis state `|1⟩`:

`(1/√r) ∑_{s<r} |u_s⟩ = |1⟩`.

It is the observation that lets phase estimation for order-finding start from `|1⟩` without
knowing `r`.
-/
theorem orderEigenstate_sum_eq_one {N : ℕ} [NeZero N] (hN : 1 < N) (x : (ZMod N)ˣ) :
    ∑ s : Fin (orderOf x), (Real.sqrt (orderOf x) : ℂ)⁻¹ • (orderEigenstate x s).vec
      = (quditBasis (1 : Fin N)).vec := sorry

end AxQM
