/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Successors
public import Rhone.Coalescent.SmcSupport.MaterialSplit

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem splitSuccessor_valid (s : State) (hs : Valid s)
    (i : Fin s.2.2.1) (x : ℝ)
    (hlo : hullLo (s.2.2.2 i).2 < x) (hhi : x < hullHi (s.2.2.2 i).2) :
    Valid (splitSuccessor s i x) := by
  classical
  let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i)
  let daughters := splitMaterial (s.2.2.2 i).2 x
  obtain ⟨hvl, hvr⟩ := splitMaterial_valid _ (hs.2.1 i) x hlo hhi
  apply valid_liveOfList s.1 (s.2.1 + 2)
    (survivors.map s.2.2.2 ++ [(s.2.1, daughters.1), (s.2.1 + 1, daughters.2)]) hs.1
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      exact hs.2.1 k
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact hvl
      · exact hvr
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      have := hs.2.2.1 k
      omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp <;> omega
  · simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · exact (List.nodup_finRange s.2.2.1).filter _ |>.map hs.2.2.2
    · intro a ha b hb
      obtain ⟨k, hk, hk'⟩ := List.mem_map.mp ha
      have hka := hs.2.2.1 k
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl <;> rw [← hk'] <;> dsimp at * <;> omega

end Rhone.Coalescent.SmcSupport
