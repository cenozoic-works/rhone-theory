/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitEpochGeometry

/-! # Old clock epochs and the record indices of the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionRun_final_old_record (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (hn : n ≤ N + 1) :
    (extractOneSplitSkeleton N h).1
      ⟨(extractionRun N h n).mergers, (extractionRun_history_prefix N h hs n hn).bound⟩ =
        (extractionRun N h n).old := by
  change (extractionRun N h (N + 1)).oldHistory _ = _
  rw [extractionRun_history_stable N h n (N + 1) hn le_rfl _ le_rfl]
  exact (extractionRun_history_prefix N h hs n hn).current

theorem extractionRun_final_history_clade (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (hn : n ≤ N + 1) (a : ℕ) :
    historyClade N (extractOneSplitSkeleton N h).1 (extractionRun N h n).mergers a =
      extractionClade (extractionRun N h n).oldLabels a := by
  classical
  ext b
  simp only [historyClade, extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← extractionRun_final_old_labels N h hs n hn b]

theorem extractionRun_old_clock_interval (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (hn : n < N + 1) (hm : (extractionRun N h n).mergers < N - 1)
    (q : ℝ) (hlo : (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.1 ≤ q)
    (hhi : q < (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩).1.1) :
    ((extractOneSplitSkeleton N h).1
      ⟨(extractionRun N h n).mergers, (extractionRun_history_prefix N h hs n
        (by omega)).bound⟩).1.1 ≤ q ∧
    q < ((extractOneSplitSkeleton N h).1
      ⟨(extractionRun N h n).mergers + 1, by omega⟩).1.1 := by
  constructor
  · rw [extractionRun_final_old_record N h hs n (by omega)]
    exact (extractionRun_clock_le N h hs n (by omega)).trans hlo
  · apply hhi.trans_le
    exact extractionRun_future_clock_ge N h hs n (N + 1) hn (by omega) le_rfl _
      (by change (extractionRun N h n).mergers < (extractionRun N h n).mergers + 1; omega)
      (by rw [extractionRun_final_mergers N h hs]; exact Nat.succ_le_of_lt hm)

theorem oneSplitARGPrefixLaw_history_supported (N : ℕ) (R : ℝ) :
    ∀ᵐ h ∂oneSplitARGPrefixLaw N R,
      KingmanHistorySupported N (extractOneSplitSkeleton N h).1 := by
  filter_upwards [oneSplitARGPrefixLaw_supported N R] with h hs
  exact extractOneSplitSkeleton_history_supported N h hs

end Rhone.Coalescent.SmcPrime
