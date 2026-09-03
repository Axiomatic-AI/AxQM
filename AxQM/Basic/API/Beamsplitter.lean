/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.DualRail
import AxQM.Basic.API.Swap

/-!
# AxQM.Basic.API — the dual-rail beamsplitter

The **beamsplitter** acting on a dual-rail single-photon qubit (Nielsen & Chuang §7.4.2). A
beamsplitter couples two optical modes; on the single-photon dual-rail manifold
`{|0_L⟩ = |01⟩, |1_L⟩ = |10⟩}` it performs the real rotation
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- `⟨01|01⟩ = 1`: the logical-zero codeword is a unit vector. (Not `@[simp]`: simp already
reduces `inner ℂ dualRailZero.vec dualRailZero.vec` via the `.vec` unfolds, so this is used by name
in the rank-one algebra below.) -/
theorem dualRailZero_inner_self :
    (inner ℂ dualRailZero.vec dualRailZero.vec : ℂ) = 1 := by
  rw [dualRailZero_vec, qubitBasis_tmul_inner]; simp

/-- `⟨10|10⟩ = 1`: the logical-one codeword is a unit vector. (Not `@[simp]`; used by name.) -/
theorem dualRailOne_inner_self :
    (inner ℂ dualRailOne.vec dualRailOne.vec : ℂ) = 1 := by
  rw [dualRailOne_vec, qubitBasis_tmul_inner]; simp

/-- `⟨10|01⟩ = 0`: the dual-rail codewords are orthogonal (the reverse of
`dualRailZero_inner_dualRailOne`). (Not `@[simp]`; used by name.) -/
theorem dualRailOne_inner_dualRailZero :
    (inner ℂ dualRailOne.vec dualRailZero.vec : ℂ) = 0 := by
  rw [dualRailOne_vec, dualRailZero_vec, qubitBasis_tmul_inner]; simp

/-- The squared norm of a dual-rail superposition, unconditionally: `‖c₀|01⟩ + c₁|10⟩‖² =
‖c₀‖² + ‖c₁‖²` (the codewords are orthonormal). The amplitude form `norm_dualRailVec` is the special
case with the amplitude constraint. -/
theorem norm_dualRailVec_sq (c0 c1 : ℂ) :
    ‖dualRailVec c0 c1‖ ^ 2 = ‖c0‖ ^ 2 + ‖c1‖ ^ 2 := by
  rw [dualRailVec, norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, dualRailZero.normalized,
    dualRailOne.normalized, inner_smul_left, inner_smul_right, dualRailZero_inner_dualRailOne]
  simp only [mul_one, mul_zero, map_zero, add_zero]

/-- The **projector onto the dual-rail plane** `span{|01⟩, |10⟩}`:
`P = |01⟩⟨01| + |10⟩⟨10|`. -/
def dualRailPlaneProj : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  InnerProductSpace.rankOne ℂ dualRailZero.vec dualRailZero.vec
    + InnerProductSpace.rankOne ℂ dualRailOne.vec dualRailOne.vec

/-- The **rotation generator** of the dual-rail plane. -/
def dualRailRotGen : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  InnerProductSpace.rankOne ℂ dualRailOne.vec dualRailZero.vec
    - InnerProductSpace.rankOne ℂ dualRailZero.vec dualRailOne.vec

/-- `P² = P`: the dual-rail plane projector is idempotent (the cross terms vanish by codeword
orthogonality). -/
theorem dualRailPlaneProj_mul_self : dualRailPlaneProj * dualRailPlaneProj = dualRailPlaneProj := by
  simp only [dualRailPlaneProj, add_mul, mul_add, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    add_zero, zero_add]

/-- `P G = G`: the projector fixes the in-plane generator. -/
theorem dualRailPlaneProj_mul_rotGen : dualRailPlaneProj * dualRailRotGen = dualRailRotGen := by
  simp only [dualRailPlaneProj, dualRailRotGen, add_mul, mul_sub, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    add_zero, zero_add]

/-- `G P = G`: the projector fixes the in-plane generator (on the right). -/
theorem dualRailRotGen_mul_planeProj : dualRailRotGen * dualRailPlaneProj = dualRailRotGen := by
  simp only [dualRailPlaneProj, dualRailRotGen, mul_add, sub_mul, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    sub_zero, zero_sub]
  abel

/-- `G² = -P`: squaring the generator gives minus the plane projector (the `σ₊σ₋ = P₁`,
`σ₋σ₊ = P₀` cross terms combine to `-(P₀ + P₁) = -P`; the diagonal squares vanish). -/
theorem dualRailRotGen_mul_self : dualRailRotGen * dualRailRotGen = -dualRailPlaneProj := by
  simp only [dualRailPlaneProj, dualRailRotGen, mul_sub, sub_mul, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    sub_zero, zero_sub, neg_add]
  abel

/-- `star P = P`: the plane projector is self-adjoint (`adjoint_rankOne` fixes each diagonal
rank-one term). -/
theorem star_dualRailPlaneProj : star dualRailPlaneProj = dualRailPlaneProj := by
  simp only [dualRailPlaneProj, star_add, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]

/-- `star G = -G`: the generator is anti-self-adjoint (`adjoint_rankOne` swaps the two off-diagonal
rank-ones). -/
theorem star_dualRailRotGen : star dualRailRotGen = -dualRailRotGen := by
  simp only [dualRailRotGen, star_sub, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]
  abel

/-- The **beamsplitter operator** on the dual-rail space, mixing angle `θ`:
`B(θ) = 1 + (cos θ - 1)·P + sin θ·G`, the planar rotation of `span{|01⟩, |10⟩}` by `θ` (and identity
on the orthogonal complement `span{|00⟩, |11⟩}`). On the logical manifold it is the real rotation
`[[cos θ, -sin θ]; [sin θ, cos θ]]` of Nielsen & Chuang eq. 7.35. -/
def beamSplitterDualRailOp (θ : ℝ) : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  1 + ((Real.cos θ : ℂ) - 1) • dualRailPlaneProj + (Real.sin θ : ℂ) • dualRailRotGen

/-- **Angle addition (group law):** `B(α) B(β) = B(α + β)`. The plane rotates by the sum of the
angles; the identity part off the plane is untouched. -/
theorem beamSplitterDualRailOp_comp (α β : ℝ) :
    beamSplitterDualRailOp α * beamSplitterDualRailOp β = beamSplitterDualRailOp (α + β) := by
  simp only [beamSplitterDualRailOp, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, dualRailPlaneProj_mul_self, dualRailPlaneProj_mul_rotGen,
    dualRailRotGen_mul_planeProj, dualRailRotGen_mul_self, smul_neg]
  match_scalars <;>
    (try simp only [Complex.cos_add, Complex.sin_add]) <;> ring

/-- `B(0) = 1`: the zero-angle beamsplitter is the identity (`cos 0 = 1`, `sin 0 = 0`). -/
theorem beamSplitterDualRailOp_zero : beamSplitterDualRailOp 0 = 1 := by
  simp [beamSplitterDualRailOp]

/-- `star B(θ) = B(-θ)`: the beamsplitter's adjoint is the reverse rotation (`cos` even, `sin` odd,
`star P = P`, `star G = -G`). -/
theorem star_beamSplitterDualRailOp (θ : ℝ) :
    star (beamSplitterDualRailOp θ) = beamSplitterDualRailOp (-θ) := by
  have hcos : star ((Real.cos θ : ℂ)) = (Real.cos θ : ℂ) := Complex.conj_ofReal _
  have hsin : star ((Real.sin θ : ℂ)) = (Real.sin θ : ℂ) := Complex.conj_ofReal _
  have hc : star ((Real.cos θ : ℂ) - 1) = (Real.cos θ : ℂ) - 1 := by
    rw [star_sub, star_one, hcos]
  rw [beamSplitterDualRailOp, beamSplitterDualRailOp, star_add, star_add, star_smul, star_smul,
    star_one, star_dualRailPlaneProj, star_dualRailRotGen, hc, hsin, Real.cos_neg, Real.sin_neg]
  push_cast
  module

/-- **The beamsplitter operator is unitary.** From `star B(θ) = B(-θ)` and the group law:
`star B(θ) · B(θ) = B(-θ) B(θ) = B(0) = 1`, and symmetrically on the other side. -/
theorem beamSplitterDualRailOp_mem_unitary (θ : ℝ) :
    beamSplitterDualRailOp θ ∈ unitary ((qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space) := by
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [star_beamSplitterDualRailOp, beamSplitterDualRailOp_comp, neg_add_cancel,
      beamSplitterDualRailOp_zero]
  · rw [star_beamSplitterDualRailOp, beamSplitterDualRailOp_comp, add_neg_cancel,
      beamSplitterDualRailOp_zero]

/-- The **beamsplitter** on a dual-rail single-photon qubit, as a closed-system `Evolution` of
`qubit ⊗ qubit` (Nielsen & Chuang §7.4.2). Its operator is the planar rotation
`beamSplitterDualRailOp θ`; unitarity is `beamSplitterDualRailOp_mem_unitary`. -/
def beamSplitterDualRail (θ : ℝ) : Evolution (qubit ⊗ qubit) where
  op := beamSplitterDualRailOp θ
  unitary := beamSplitterDualRailOp_mem_unitary θ

@[simp]
theorem beamSplitterDualRail_op (θ : ℝ) :
    (beamSplitterDualRail θ).op = beamSplitterDualRailOp θ := rfl

/-- **The beamsplitter's action on `|01⟩`:** `B(θ)|01⟩ = cos θ|01⟩ + sin θ|10⟩` (N&C 7.35). -/
theorem beamSplitterDualRailOp_apply_dualRailZero (θ : ℝ) :
    beamSplitterDualRailOp θ dualRailZero.vec
      = (Real.cos θ : ℂ) • dualRailZero.vec + (Real.sin θ : ℂ) • dualRailOne.vec := by
  rw [beamSplitterDualRailOp, dualRailPlaneProj, dualRailRotGen]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply,
    dualRailZero_inner_self, dualRailOne_inner_dualRailZero, one_smul, zero_smul, add_zero,
    sub_zero]
  module

/-- **The beamsplitter's action on `|10⟩`:** `B(θ)|10⟩ = -sin θ|01⟩ + cos θ|10⟩` (N&C 7.35). -/
theorem beamSplitterDualRailOp_apply_dualRailOne (θ : ℝ) :
    beamSplitterDualRailOp θ dualRailOne.vec
      = -(Real.sin θ : ℂ) • dualRailZero.vec + (Real.cos θ : ℂ) • dualRailOne.vec := by
  rw [beamSplitterDualRailOp, dualRailPlaneProj, dualRailRotGen]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply,
    dualRailOne_inner_self, dualRailZero_inner_dualRailOne, one_smul, zero_smul, zero_sub]
  module

/-- **The beamsplitter's action on a dual-rail superposition** (vector level):
`B(θ)(c₀|01⟩ + c₁|10⟩) = (cos θ·c₀ - sin θ·c₁)|01⟩ + (sin θ·c₀ + cos θ·c₁)|10⟩`. -/
theorem beamSplitterDualRailOp_apply_dualRailVec (θ : ℝ) (c0 c1 : ℂ) :
    beamSplitterDualRailOp θ (dualRailVec c0 c1)
      = dualRailVec ((Real.cos θ : ℂ) * c0 - (Real.sin θ : ℂ) * c1)
          ((Real.sin θ : ℂ) * c0 + (Real.cos θ : ℂ) * c1) := by
  rw [dualRailVec, dualRailVec, map_add, map_smul, map_smul,
    beamSplitterDualRailOp_apply_dualRailZero, beamSplitterDualRailOp_apply_dualRailOne]
  module

/-- **Congruence for `dualRailVec` in both amplitudes:** equal amplitudes give equal dual-rail
vectors. -/
theorem dualRailVec_congr {a a' b b' : ℂ} (ha : a = a') (hb : b = b') :
    dualRailVec a b = dualRailVec a' b' := by rw [ha, hb]

/-- **The operator action of the balanced Mach–Zehnder composition** `B(-π/4) · P(φ) · B(π/4)` on a
dual-rail vector: it sends `c₀·|01⟩ + c₁·|10⟩` to the vector with amplitudes `½((e^{iφ}+1)c₀ +
(1-e^{iφ})c₁)` on `|01⟩` and `½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁)` on `|10⟩`.
(Nielsen & Chuang, Exercise 7.10 part 2.) -/
theorem machZehnderDualRail_op_apply_dualRailVec (φ : ℝ) (c0 c1 : ℂ) :
    (beamSplitterDualRail (-(Real.pi / 4))).op
        (((phaseShiftGate φ).onRight qubit).op
          ((beamSplitterDualRail (Real.pi / 4)).op (dualRailVec c0 c1)))
      = dualRailVec
          (2⁻¹ * ((Complex.exp ((φ : ℂ) * Complex.I) + 1) * c0
            + (1 - Complex.exp ((φ : ℂ) * Complex.I)) * c1))
          (2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * Complex.I)) * c0
            + (Complex.exp ((φ : ℂ) * Complex.I) + 1) * c1)) := by
  simp only [beamSplitterDualRail_op]
  rw [beamSplitterDualRailOp_apply_dualRailVec, phaseShiftGate_onRight_op_dualRailVec,
    beamSplitterDualRailOp_apply_dualRailVec]
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt] <;> norm_num
  apply dualRailVec_congr
  · rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring_nf
    linear_combination
      (c0 * Complex.exp ((φ : ℂ) * Complex.I) / 4 + c0 / 4
        - c1 * Complex.exp ((φ : ℂ) * Complex.I) / 4 + c1 / 4) * h2
  · rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring_nf
    linear_combination
      (c0 / 4 - c0 * Complex.exp ((φ : ℂ) * Complex.I) / 4
        + c1 * Complex.exp ((φ : ℂ) * Complex.I) / 4 + c1 / 4) * h2

/-- **The mirror (mode `SWAP`) exchanges the amplitudes of a dual-rail superposition:** `SWAP(c₀|01⟩
+ c₁|10⟩) = c₁|01⟩ + c₀|10⟩`. -/
theorem swap_op_dualRailVec (c0 c1 : ℂ) :
    (Evolution.swap (S := qubit)).op (dualRailVec c0 c1) = dualRailVec c1 c0 := by
  simp only [dualRailVec, dualRailZero_vec, dualRailOne_vec, PureState.tmul_vec, map_add, map_smul,
    Evolution.swap_op_tmul]
  rw [add_comm]

/-- **The phase-shifter-free optical Hadamard** on a dual-rail single-photon qubit (Nielsen & Chuang
Exercise 7.13, part 2). It realises the Hadamard *exactly*, with no residual global phase, which
is precisely why no phase shifters are necessary. -/
def opticalHadamardMirror : Evolution (qubit ⊗ qubit) :=
  (Evolution.swap (S := qubit)).comp (beamSplitterDualRail (Real.pi / 4))

/-- **Operator action of the mirror-Hadamard on a dual-rail superposition:** it sends
`c₀|01⟩ + c₁|10⟩` to `(√2/2)(c₀ + c₁)|01⟩ + (√2/2)(c₀ - c₁)|10⟩` — *exactly* the Hadamard amplitude
map `(c₀, c₁) ↦ ((c₀+c₁)/√2, (c₀-c₁)/√2)`, with no global phase. The beamsplitter rotates
`(c₀, c₁)` to `(√2/2)(c₀-c₁, c₀+c₁)` (`cos(π/4) = sin(π/4) = √2/2`) and the mirror then swaps the
two amplitudes. -/
theorem opticalHadamardMirror_op_apply_dualRailVec (c0 c1 : ℂ) :
    opticalHadamardMirror.op (dualRailVec c0 c1)
      = dualRailVec ((Real.sqrt 2 : ℂ) / 2 * (c0 + c1)) ((Real.sqrt 2 : ℂ) / 2 * (c0 - c1)) := by
  rw [opticalHadamardMirror, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    beamSplitterDualRail_op, beamSplitterDualRailOp_apply_dualRailVec, swap_op_dualRailVec]
  apply dualRailVec_congr
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring

/-- **The mirror-Hadamard preserves normalisation:** the transformed amplitudes
`((√2/2)(c₀+c₁), (√2/2)(c₀-c₁))` again satisfy `‖·‖² + ‖·‖² = 1`, since `opticalHadamardMirror` is a
unitary `Evolution` (a beamsplitter composed with the `SWAP`) and the codewords are orthonormal. -/
theorem opticalHadamardMirror_amplitudes_normalized (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖(Real.sqrt 2 : ℂ) / 2 * (c0 + c1)‖ ^ 2 + ‖(Real.sqrt 2 : ℂ) / 2 * (c0 - c1)‖ ^ 2 = 1 := by
  have hnorm : ‖dualRailVec ((Real.sqrt 2 : ℂ) / 2 * (c0 + c1))
      ((Real.sqrt 2 : ℂ) / 2 * (c0 - c1))‖ = 1 := by
    rw [← opticalHadamardMirror_op_apply_dualRailVec, opticalHadamardMirror.norm_op_apply]
    exact norm_dualRailVec c0 c1 h
  rw [← norm_dualRailVec_sq, hnorm, one_pow]

end AxQM
