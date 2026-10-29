/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitHistorySupport

/-! # Retained old history slots persist through all later events -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_mergers_le {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) : z.mergers ≤ (extractionStep z pre next).mergers := by
  classical
  unfold extractionStep
  split <;> simp only
  · exact le_rfl
  · exact le_rfl
  · split <;> simp only
    · exact le_rfl
    · exact Nat.le_add_right _ _

theorem extractionStep_history_stable {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (k : Fin N) (hk : k.val ≤ z.mergers) :
    (extractionStep z pre next).oldHistory k = z.oldHistory k := by
  classical
  unfold extractionStep
  split <;> simp only
  split <;> simp only
  split
  · apply Function.update_of_ne
    intro he
    have hv := congrArg Fin.val he
    change k.val = z.mergers + 1 at hv
    omega
  · rfl

theorem extractionRun_mergers_mono (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n m : ℕ)
    (hnm : n ≤ m) (hm : m ≤ N + 1) :
    (extractionRun N h n).mergers ≤ (extractionRun N h m).mergers := by
  induction m with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact le_rfl
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n
      exact le_rfl
    · have hnm' : n ≤ m := by omega
      exact (ih hnm' (by omega)).trans (by
        rw [extractionRun_succ N h m (by omega)]
        exact extractionStep_mergers_le _ _ _)

theorem extractionRun_history_stable (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n m : ℕ)
    (hnm : n ≤ m) (hm : m ≤ N + 1) (k : Fin N)
    (hk : k.val ≤ (extractionRun N h n).mergers) :
    (extractionRun N h m).oldHistory k = (extractionRun N h n).oldHistory k := by
  induction m with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n
      rfl
    · have hnm' : n ≤ m := by omega
      rw [extractionRun_succ N h m (by omega), extractionStep_history_stable]
      · exact ih hnm' (by omega)
      · exact hk.trans (extractionRun_mergers_mono N h n m hnm' (by omega))

end Rhone.Coalescent.SmcPrime
