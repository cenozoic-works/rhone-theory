/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Block
public import Rhone.Algebra.KilledSystem.UniqueGeneric

/-! # Uniqueness: the killed-PIM system has at most one solution -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

theorem unique_aux (Δ : St → L)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s
      = rhsC 1 (thA * piA0) (thA * piA1) (thB * piB0) (thB * piB1) rhoL Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0) :
    ∀ s ∈ closureList, Δ s = 0 := by
  exact unique_aux_generic thA thB rhoL piA0 piA1 piB0 piB1 Δ
    ne_lhs02 ne_lhs20 ne_lhs11 ne_d1_12 ne_d1_21 ne_E12 ne_E21
    ne_d2_22 ne_W22 ne_W4_22 ne_D22 hrec hbd

theorem unique_of_isSolution {q q2 : St → L} (h : IsSolution q) (h2 : IsSolution q2) :
    ∀ s ∈ closureList, q s = q2 s := by
  intro s hs
  have key := unique_aux (fun z => q z - q2 z) ?_ ?_ s hs
  · exact sub_eq_zero.mp key
  · intro t ht
    have e := congrArg₂ (· - ·) (h.1 t ht) (h2.1 t ht)
    rw [rhsC_sub] at e
    change lhsC thA thB rhoL t * (q t - q2 t) = _
    rw [mul_sub]
    exact e
  · intro t ht
    rw [h.2 t ht, h2.2 t ht, sub_self]

end Rhone.Algebra.KilledSystem
