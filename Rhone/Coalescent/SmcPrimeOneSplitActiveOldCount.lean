/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitOldClockIntervals

/-! # Counts of active old branches through split and pair events -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ExtractionInventory.active_old_count {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (hs : Valid s)
    (hd : z.detached = none) (hc : 2 ≤ s.2.2.1) : 2 ≤ z.old.1.2.2.1 := by
  let i : Fin s.2.2.1 := ⟨0, by omega⟩
  let j : Fin s.2.2.1 := ⟨1, by omega⟩
  obtain ⟨a, u, haf, hag, _⟩ := h.parent_lookup i (by rw [hd]; exact nofun)
  obtain ⟨b, v, hbf, hbg, _⟩ := h.parent_lookup j (by rw [hd]; exact nofun)
  have hne : u ≠ v := by
    intro he
    have hge : z.oldLabels a = z.oldLabels b := by rw [hag, hbg, he]
    have hfe := (h.2.2.2.2 a b).mpr hge
    have heij := congrArg Fin.val (hs.2.2.2 (haf.symm.trans (hfe.trans hbf)))
    change (0 : ℕ) = 1 at heij
    omega
  by_contra hn
  have hval : u.val = v.val := by have := u.isLt; have := v.isLt; omega
  exact hne (Fin.ext hval)

theorem ARGTransition.split_active_count {pre next : AugmentedState}
    (ht : ARGTransition (pre, next)) (he : next.2.2 ∈ splitSet) : 2 ≤ pre.1.2.2.1 := by
  classical
  rcases ht with ht | ⟨hm, _⟩
  · unfold KingmanTransition at ht
    split_ifs at ht with hm
    · obtain ⟨_, _, _, hev, _, _⟩ := ht
      rw [hev] at he
      cases he
    · rw [ht.2] at he
      cases he
  · exact hm

end Rhone.Coalescent.SmcPrime
