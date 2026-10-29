/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightEpochGeometry
public import Rhone.Coalescent.SmcSupport.SingleCutReachableExposure

/-! # Root bounds and right carrier counts from finite completion of the prefix -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractOneSplitSkeleton_root_bounds (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    rootHeight (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) ≤
        (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1 ∧
      rootHeight (oneSplitPostTree (extractOneSplitSkeleton N h)) ≤
        (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1 := by
  let z := extractionRun N h (N + 1)
  let η := extractOneSplitSkeleton N h
  let ω := kingmanCompletion N η.1
  have hp := extractionRun_history_prefix N h hs (N + 1) le_rfl
  have hk := extractOneSplitSkeleton_history_supported N h hs
  have he : (fun j : Fin N => ω j.val) = η.1 := by
    funext j
    exact kingmanCompletion_prefix N η.1 j.val j.isLt
  have hm : z.mergers = N - 1 := extractionRun_final_mergers N h hs
  have hb : N - 1 < N := by have := hs.sample_pos; omega
  have hcur : η.1 ⟨N - 1, hb⟩ = z.old := by
    have hi : (⟨N - 1, hb⟩ : Fin N) = ⟨z.mergers, hp.bound⟩ := Fin.ext hm.symm
    rw [hi]
    exact hp.current
  have hr := metric_tree_root_height_of_pos N ω hk.completion_init
    hk.completion_valid hk.completion_step hs.sample_pos
  rw [he] at hr
  dsimp only [ω] at hr
  rw [kingmanCompletion_prefix N η.1 (N - 1) hb, hcur] at hr
  have hroot : rootHeight (metricTreeFromHistory N η.1) ≤
      (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1 := by
    rw [hr]
    exact extractionRun_clock_le N h hs (N + 1) le_rfl
  refine ⟨hroot, ?_⟩
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  have hatt : η.2.2.2.2.1 ≤ (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1 := by
    dsimp only [η]
    rw [w.attach_field]
    simp only
    rw [extractionPrefixExtension_prefix N h (w.attachStep + 1) w.attach_bound]
    exact hs.clock_mono _ _ w.attach_bound le_rfl
  obtain ⟨_, hta, htr, _, _, _⟩ := extractOneSplitSkeleton_cut_geometry N h hs
  rw [oneSplitPostTree_regraft]
  exact (regraft_root_height_le _ _ _ _ _ (metric_tree_from_history_normalized N _) htr hta).trans
    (max_le hroot hatt)

theorem reachable_right_carrier_iff (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (s : State) (hs : ZeroSplitReachable s ∨ OneSplitReachable x s)
    (q : ℝ) (hqx : x ≤ q) (hq1 : q < 1) (i : Fin s.2.2.1) :
    materialContains (s.2.2.2 i).2 q ↔ materialContains (s.2.2.2 i).2 x := by
  have htag : ∃ u, Tagged x (s.2.2.2 i).2 u := by
    rcases hs with hz | ho
    · exact ⟨.full, Tagged.full _ (zeroSplit_full hz i)⟩
    · exact one_split_tagged x hx0 hx1 ho i
  obtain ⟨u, hu⟩ := htag
  rw [tagged_contains x hx0 hx1 hu q, tagged_contains x hx0 hx1 hu x]
  cases u <;> simp only [Rhone.Coalescent.SmcSpan.lo, Rhone.Coalescent.SmcSpan.hi] <;> grind

end Rhone.Coalescent.SmcPrime
