/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Block
public import Rhone.Algebra.KilledSystem.UniqueGeneric

/-! # Uniqueness at arbitrary parameters via the shared field-generic certificates -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystemULast

open KilledSystem

theorem unique_auxG (tA tB r pA0 pA1 pB0 pB1 : L) (Δ : St → L)
    (ne_lhs02 : (2 + 2 * tB : L) ≠ 0)
    (ne_lhs20 : (2 + 2 * tA : L) ≠ 0)
    (ne_lhs11 : (2 + tA + tB : L) ≠ 0)
    (ne_d1_12 : (2 + tA + 2 * tB + r : L) ≠ 0)
    (ne_d1_21 : (2 + 2 * tA + tB + r : L) ≠ 0)
    (ne_E12 : ((6 + tA + 2 * tB) * (2 + tA + 2 * tB + r) - 4 * r : L) ≠ 0)
    (ne_E21 : ((6 + 2 * tA + tB) * (2 + 2 * tA + tB + r) - 4 * r : L) ≠ 0)
    (ne_d2_22 : (2 + 2 * tA + 2 * tB + 2 * r : L) ≠ 0)
    (ne_W22 : ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) : L) ≠ 0)
    (ne_W4_22 : ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r : L) ≠ 0)
    (ne_D22 : ((12 + 2 * tA + 2 * tB)
        * ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r)
      - 8 * r * (2 + 2 * tA + 2 * tB + 2 * r) : L) ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsC tA tB r s * Δ s
      = rhsC 1 (tA * pA0) (tA * pA1) (tB * pB0) (tB * pB1) r Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0) :
    ∀ s ∈ closureList, Δ s = 0 :=
  unique_aux_generic tA tB r pA0 pA1 pB0 pB1 Δ ne_lhs02 ne_lhs20 ne_lhs11 ne_d1_12 ne_d1_21 ne_E12
    ne_E21 ne_d2_22 ne_W22 ne_W4_22 ne_D22 hrec hbd

theorem unique_auxU (Δ : St → L)
    (hrec : ∀ s ∈ recStates, lhsC thAu thBu rhoU s * Δ s
      = rhsC 1 (thAu * piA0) (thAu * piA1) (thBu * piB0) (thBu * piB1) rhoU Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0) :
    ∀ s ∈ closureList, Δ s = 0 :=
  unique_auxG thAu thBu rhoU piA0 piA1 piB0 piB1 Δ neU_lhs02 neU_lhs20 neU_lhs11 neU_d1_12
    neU_d1_21 neU_E12 neU_E21 neU_d2_22 neU_W22 neU_W4_22 neU_D22 hrec hbd

theorem unique_of_isSolutionU {q q2 : St → L} (h : IsSolutionU q) (h2 : IsSolutionU q2) :
    ∀ s ∈ closureList, q s = q2 s := by
  intro s hs
  have key := unique_auxU (fun z => q z - q2 z) ?_ ?_ s hs
  · exact sub_eq_zero.mp key
  · intro t ht
    have e := congrArg₂ (· - ·) (h.1 t ht) (h2.1 t ht)
    rw [rhsC_sub] at e
    change lhsC thAu thBu rhoU t * (q t - q2 t) = _
    rw [mul_sub]
    exact e
  · intro t ht
    rw [h.2 t ht, h2.2 t ht, sub_self]

end Rhone.Algebra.KilledSystemULast
