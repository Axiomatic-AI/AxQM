/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A linearly dependent triple of vectors in `ℂ²` (Nielsen & Chuang, Exercise 2.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.1
(p. 63) asks to show that the three vectors `(1, -1)`, `(1, 2)` and `(2, 1)` of
`ℂ²` are *linearly dependent*. In the book's sense (N&C (2.9)) this means some
complex linear combination of them, with at least one nonzero coefficient, is
the zero vector.
-/

namespace AxQM.Concrete

/-- The three vectors `(1, -1)`, `(1, 2)` and `(2, 1)` of `ℂ²` from Nielsen & Chuang, Exercise 2.1,
packaged as a family indexed by `Fin 3`. -/
def dependentTripleC2 : Fin 3 → EuclideanSpace ℂ (Fin 2) :=
  ![!₂[1, -1], !₂[1, 2], !₂[2, 1]]

/-- **Nielsen & Chuang, Exercise 2.1.** The vectors `(1, -1)`, `(1, 2)` and `(2, 1)` of `ℂ²` are
linearly dependent: they are *not* linearly independent. -/
theorem not_linearIndependent_dependentTripleC2 :
    ¬ LinearIndependent ℂ dependentTripleC2 := sorry

end AxQM.Concrete
