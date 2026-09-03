/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Mul

/-!
# Operator convexity of the ring inverse on a shifted cone

## Main results

* `CStarAlgebra.convexOn_ringInverse_add_of_isStrictlyPositive`: `c ↦ Ring.inverse (s + c)` is
  operator convex on the nonnegative cone, for strictly positive `s`.
* `CStarAlgebra.convexOn_ringInverse_one_add`: the case `s = 1`.

-/

@[expose] public section

namespace CStarAlgebra
section
open CFC
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator-convex function `c ↦ Ring.inverse (s + c)` on the nonnegative cone, for any
strictly positive `s`. -/
public lemma convexOn_ringInverse_add_of_isStrictlyPositive {s : A} (hs : IsStrictlyPositive s) :
    ConvexOn ℝ (Set.Ici (0 : A)) (fun c ↦ Ring.inverse (s + c)) := by
  refine ⟨convex_Ici 0, fun a (ha : 0 ≤ a) b (hb : 0 ≤ b) α β hα hβ hαβ ↦ ?_⟩
  have hsab : s + (α • a + β • b) = α • (s + a) + β • (s + b) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hαβ, one_smul]
  change Ring.inverse (s + (α • a + β • b)) ≤ α • Ring.inverse (s + a) + β • Ring.inverse (s + b)
  rw [hsab]
  exact convexOn_ringInverse.2 (hs.add_nonneg ha) (hs.add_nonneg hb) hα hβ hαβ

end
end CStarAlgebra

namespace CStarAlgebra
section
open CFC
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator-convex function `c ↦ Ring.inverse (1 + c)` on the nonnegative cone. -/
public lemma convexOn_ringInverse_one_add :
    ConvexOn ℝ (Set.Ici (0 : A)) (fun c ↦ Ring.inverse (1 + c)) :=
  convexOn_ringInverse_add_of_isStrictlyPositive isStrictlyPositive_one

end
end CStarAlgebra
