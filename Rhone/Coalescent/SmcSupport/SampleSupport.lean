/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Agreement

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

def SplitEvent (e : Event) : Prop := ∃ i x, e = .inr (.inr (i, x))

theorem sampleStep_zero_support (mode : Mode) (R : ℝ) {s : State}
    (hs : ZeroSplitReachable s) (u : Noise)
    (hu0 : 0 < u 2) (hu1 : u 2 < 1) :
    ZeroSplitReachable (sampleStep mode R s u).1 ∨
      ∃ x, 0 < x ∧ x < 1 ∧ OneSplitReachable x (sampleStep mode R s u).1 := by
  classical
  unfold sampleStep
  split_ifs
  · exact Or.inl hs
  · cases ha : selectedAction mode R s u with
    | none => exact Or.inl hs
    | some a =>
      cases a with
      | inl ij =>
        exact Or.inl (ZeroSplitReachable.clock
          (ZeroSplitReachable.coal hs ij.1 ij.2) _)
      | inr i =>
        have hf := zeroSplit_full hs i
        obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ 0 1 (by norm_num) hf
        have hlen : hullLength (s.2.2.2 i).2 = 1 := by simp [hullLength, hlo, hhi]
        simp only [hlo, hlen, one_mul, zero_add]
        exact Or.inr ⟨u 2, hu0, hu1,
          OneSplitReachable.clock (OneSplitReachable.split hs i) _⟩

theorem sampleStep_one_support (mode : Mode) (R x : ℝ) {s : State}
    (hs : OneSplitReachable x s) (u : Noise) :
    OneSplitReachable x (sampleStep mode R s u).1 ∨
      SplitEvent (sampleStep mode R s u).2.2 := by
  classical
  unfold sampleStep
  split_ifs
  · exact Or.inl hs
  · cases ha : selectedAction mode R s u with
    | none => exact Or.inl hs
    | some a =>
      cases a with
      | inl ij =>
        exact Or.inl (OneSplitReachable.clock
          (OneSplitReachable.coal hs ij.1 ij.2) _)
      | inr i =>
        exact Or.inr ⟨i.val, _, rfl⟩

end Rhone.Coalescent.SmcSupport
