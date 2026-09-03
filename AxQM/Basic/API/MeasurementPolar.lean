/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.PolarUnitary

/-!
# AxQM — polar form of measurement operators

**Nielsen–Chuang Exercise 2.63**: for a measurement described by measurement operators `Mₘ`, there
exist *unitary* operators `Uₘ` such that `Mₘ = Uₘ √Eₘ`, where `Eₘ = Mₘ† Mₘ` is the POVM element
associated to the measurement (eq. (2.117)).
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Nielsen–Chuang Exercise 2.63 (polar form of measurement operators).** For a measurement `m :
Measurement ι S` and outcome `i`, the measurement operator `Mᵢ = m.op i` factors as `Mᵢ = Uᵢ
√Eᵢ` for some **unitary** `Uᵢ`, where `Eᵢ = m.toPOVM.elements i = Mᵢ† Mᵢ` is the associated POVM
element and `√Eᵢ = cfc Real.sqrt Eᵢ` is its positive operator square root.
-/
theorem exists_unitary_op_eq_comp_sqrt_toPOVM_elements (m : Measurement ι S) (i : ι) :
    ∃ U ∈ unitary (S →L[ℂ] S), m.op i = U.comp (cfc Real.sqrt (m.toPOVM.elements i)) := sorry

end Measurement

end AxQM
