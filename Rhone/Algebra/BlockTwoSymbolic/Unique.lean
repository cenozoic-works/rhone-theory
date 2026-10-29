/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueGeneric

/-! # Uniqueness over any field via the shared exact elimination certificates -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.BlockTwoSymbolic

open KilledSystem

theorem eq_zero_of_mulF {F : Type*} [Field F] {A x : F} (hA : A ≠ 0) (h : A * x = 0) :
    x = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hA
  · exact h'

theorem unique_auxF {F : Type*} [Field F] (tA tB r pA0 pA1 pB0 pB1 : F)
    (Δ : St → F)
    (ne_lhs02 : (2 + 2 * tB : F) ≠ 0)
    (ne_lhs20 : (2 + 2 * tA : F) ≠ 0)
    (ne_lhs11 : (2 + tA + tB : F) ≠ 0)
    (ne_d1_12 : (2 + tA + 2 * tB + r : F) ≠ 0)
    (ne_d1_21 : (2 + 2 * tA + tB + r : F) ≠ 0)
    (ne_E12 : ((6 + tA + 2 * tB) * (2 + tA + 2 * tB + r) - 4 * r : F) ≠ 0)
    (ne_E21 : ((6 + 2 * tA + tB) * (2 + 2 * tA + tB + r) - 4 * r : F) ≠ 0)
    (ne_d2_22 : (2 + 2 * tA + 2 * tB + 2 * r : F) ≠ 0)
    (ne_W22 : ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) : F) ≠ 0)
    (ne_W4_22 : ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r : F) ≠ 0)
    (ne_D22 : ((12 + 2 * tA + 2 * tB)
        * ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r)
      - 8 * r * (2 + 2 * tA + 2 * tB + 2 * r) : F) ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsC tA tB r s * Δ s
      = rhsC 1 (tA * pA0) (tA * pA1) (tB * pB0) (tB * pB1) r Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0) :
    ∀ s ∈ closureList, Δ s = 0 :=
  unique_aux_generic tA tB r pA0 pA1 pB0 pB1 Δ ne_lhs02 ne_lhs20 ne_lhs11 ne_d1_12 ne_d1_21 ne_E12
    ne_E21 ne_d2_22 ne_W22 ne_W4_22 ne_D22 hrec hbd

end Rhone.Algebra.BlockTwoSymbolic
