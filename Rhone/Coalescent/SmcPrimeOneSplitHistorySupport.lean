/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitLocalHistory
public import Rhone.Coalescent.SmcPrimeOneSplitTerminalInventory

/-! # The extracted old records are supported Kingman histories -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionRun_history_prefix (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n ≤ N + 1) :
    ExtractedHistoryPrefix N (extractionRun N h n) := by
  obtain ⟨s, hsplit, hcoal⟩ := hs.2.2.2.2.1
  induction n with
  | zero => exact extractionInitial_history_prefix N hs.sample_pos
  | succ n ih =>
    have hlt : n < N + 1 := by omega
    let k : Fin (N + 1) := ⟨n, hlt⟩
    have hpre := hs.2.1 ⟨n, Finset.mem_Iic.mpr (by omega)⟩
    have htrans := hs.2.2.1 k
    dsimp only [k] at htrans
    rw [extractionRun_succ N h n hlt]
    by_cases he : k = s
    · have hsplit' : (h ⟨n + 1, Finset.mem_Iic.mpr hn⟩).2.2 ∈ splitSet := by
        simpa only [← he] using hsplit
      obtain ⟨i, x, _, _, hev, _, _⟩ := htrans.split_case hpre hsplit'
      exact extractionStep_split_history _ _ _ (ih (by omega)) (i.val, x) hev
    · obtain ⟨i, j, hij, hev, _, _⟩ := htrans.coal_case (hcoal k he)
      by_cases hd : (extractionRun N h n).detached = some ((h
          ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.2 i).1 ∨
          (extractionRun N h n).detached = some ((h
          ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.2 j).1
      · apply extractionStep_attachment_history _ _ _ (ih (by omega)) (i.val, j.val) hev
        have hiuid : liveLabelAt (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1 i.val =
            ((h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.2 i).1 := by
          simp only [liveLabelAt, dite_eq_left i.isLt]
        have hjuid : liveLabelAt (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1 j.val =
            ((h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.2 j).1 := by
          simp only [liveLabelAt, dite_eq_left j.isLt]
        rw [hiuid, hjuid]
        rcases hd with hi | hj
        · exact ⟨_, hi, Or.inl rfl⟩
        · exact ⟨_, hj, Or.inr rfl⟩
      · exact extractionStep_old_pair_history _ _ _
          (extractionRun_inventory N h hs n (by omega)) hpre (ih (by omega))
          (extractionRun_clock_le N h hs n (by omega)) (hs.clock_lt k) i j hij hev
          (fun hi => hd (Or.inl hi)) (fun hj => hd (Or.inr hj))

theorem extractionRun_final_mergers (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h) :
    (extractionRun N h (N + 1)).mergers = N - 1 := by
  have hh := extractionRun_history_prefix N h hs (N + 1) le_rfl
  have hcount := (hh.records ⟨_, hh.bound⟩ le_rfl).2
  rw [hh.current, (extractionRun_terminal_inventory N h hs).2] at hcount
  change 1 = N - (extractionRun N h (N + 1)).mergers at hcount
  have := hh.bound
  omega

theorem extractOneSplitSkeleton_history_supported (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h) :
    KingmanHistorySupported N (extractOneSplitSkeleton N h).1 := by
  change KingmanHistorySupported N (extractionRun N h (N + 1)).oldHistory
  have hh := extractionRun_history_prefix N h hs (N + 1) le_rfl
  have hm := extractionRun_final_mergers N h hs
  refine ⟨?_, hh.initial, ?_⟩
  · intro k
    exact hh.records k (by rw [hm]; have := k.isLt; omega)
  · intro k
    exact hh.transitions k (by rw [hm]; exact k.isLt)

end Rhone.Coalescent.SmcPrime
