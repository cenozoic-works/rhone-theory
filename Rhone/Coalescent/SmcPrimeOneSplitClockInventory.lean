/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitGlobalInventory

/-! # Retained old clocks stay below the current ARG clock -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_clock_le {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (hc : z.old.1.1 ≤ pre.1.1) (ht : pre.1.1 ≤ next.1.1) :
    (extractionStep z pre next).old.1.1 ≤ next.1.1 := by
  classical
  unfold extractionStep
  split <;> simp only
  · exact hc.trans ht
  · exact hc.trans ht
  · split <;> simp only [rebuildCoal, atTime]
    · exact hc.trans ht
    · exact le_rfl

theorem OneSplitPrefixSupported.clock_lt {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)}
    (hs : OneSplitPrefixSupported N h) (k : Fin (N + 1)) :
    (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.1 <
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.1 := by
  obtain ⟨s, hsplit, hcoal⟩ := hs.2.2.2.2.1
  by_cases he : k = s
  · have hsplit' : (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).2.2
        ∈ splitSet := by simpa only [← he] using hsplit
    obtain ⟨_, _, _, _, _, _, ht⟩ :=
      (hs.2.2.1 k).split_case (hs.2.1 _) hsplit'
    exact ht
  · obtain ⟨_, _, _, _, _, ht⟩ := (hs.2.2.1 k).coal_case (hcoal k he)
    exact ht

theorem extractionRun_clock_le (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n ≤ N + 1) :
    (extractionRun N h n).old.1.1 ≤ (h ⟨n, Finset.mem_Iic.mpr hn⟩).1.1 := by
  induction n with
  | zero => rw [extractionRun_zero, hs.1]; exact le_rfl
  | succ n ih =>
    rw [extractionRun_succ N h n (by omega)]
    apply extractionStep_clock_le _ _ _ (ih (by omega))
    exact (hs.clock_lt ⟨n, by omega⟩).le

end Rhone.Coalescent.SmcPrime
