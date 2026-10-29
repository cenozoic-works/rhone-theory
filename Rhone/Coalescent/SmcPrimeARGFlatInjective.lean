/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGFlatSupport

/-! # Decoding flat ARG coordinates recovers events and clocks and is injective -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem argFlatRebuild_event (N : ℕ) (p : ARGFlatCoordinate N) (j : Fin (N + 1)) :
    (argFlatRebuild N p ⟨j.val + 1, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).2.2 =
      match p.1 j with
      | .inl ij => .inr (.inl ij)
      | .inr i => .inr (.inr (i, p.2.2)) := by
  unfold argFlatRebuild
  rw [argFlatRun, dite_eq_left j.isLt]
  cases p.1 j <;> rfl

theorem argFlatRebuild_decoded (N : ℕ) (p : ARGFlatCoordinate N) :
    argDecodedWord (argFlatRebuild N p) = p.1 := by
  funext j
  unfold argDecodedWord
  rw [argFlatRebuild_event]
  cases p.1 j <;> rfl

theorem argFlatRebuild_clock (N : ℕ) (p : ARGFlatCoordinate N) (j : Fin (N + 1)) :
    (argFlatRebuild N p ⟨j.val + 1, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.1 =
      p.2.1 j := argFlatRun_event_time _ _ _ _ j

theorem argFlatRebuild_injOn (N : ℕ) :
    Set.InjOn (argFlatRebuild N) {p : ARGFlatCoordinate N | argFlatValid N p} := by
  intro p hp q _hq he
  have hw : p.1 = q.1 := by
    rw [← argFlatRebuild_decoded N p, he, argFlatRebuild_decoded N q]
  have ht : p.2.1 = q.2.1 := by
    funext j
    rw [← argFlatRebuild_clock N p j, he, argFlatRebuild_clock N q j]
  obtain ⟨s,⟨i,hi⟩,_⟩ := hp.1
  have hs : (argFlatRebuild N p ⟨s.val + 1, Finset.mem_Iic.mpr (by have := s.isLt; omega)⟩).2.2 =
      (argFlatRebuild N q ⟨s.val + 1, Finset.mem_Iic.mpr (by have := s.isLt; omega)⟩).2.2 :=
    congrArg (fun h : ARGPrefix (N + 1) =>
      (h ⟨s.val + 1, Finset.mem_Iic.mpr (by have := s.isLt; omega)⟩).2.2) he
  rw [argFlatRebuild_event, argFlatRebuild_event, ← hw, hi] at hs
  change (.inr (.inr (i, p.2.2)) : Event) = .inr (.inr (i, q.2.2)) at hs
  have hix : (i, p.2.2) = (i, q.2.2) := Sum.inr.inj (Sum.inr.inj hs)
  have hx : p.2.2 = q.2.2 := congrArg (fun a : ℕ × ℝ => a.2) hix
  exact Prod.ext hw (Prod.ext ht hx)
end Rhone.Coalescent.SmcPrime
