/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitHistoryPersistence

/-! # Future old merger clocks lie at later event times -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_new_slot {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (k : Fin N) (hk : z.mergers < k.val)
    (hk' : k.val ≤ (extractionStep z pre next).mergers) :
    (extractionStep z pre next).oldHistory k = (extractionStep z pre next).old ∧
      (extractionStep z pre next).old.1.1 = next.1.1 := by
  classical
  cases hev : next.2.2 with
  | inl u => simp only [extractionStep, hev] at hk'; omega
  | inr a =>
    cases a with
    | inr ix => simp only [extractionStep, hev] at hk'; omega
    | inl ij =>
      by_cases hd : ∃ d, z.detached = some d ∧
          (d = liveLabelAt pre.1 ij.1 ∨ d = liveLabelAt pre.1 ij.2)
      · simp only [extractionStep, hev, ite_eq_left hd] at hk'
        omega
      · simp only [extractionStep, hev, ite_eq_right hd] at hk' ⊢
        have he : k.val = z.mergers + 1 := by omega
        have hb : z.mergers + 1 < N := by have := k.isLt; omega
        simp only [dite_eq_left hb]
        have hek : k = ⟨z.mergers + 1, hb⟩ := Fin.ext he
        subst k
        rw [Function.update_self]
        exact ⟨rfl, rfl⟩

theorem OneSplitPrefixSupported.clock_mono {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)}
    (hs : OneSplitPrefixSupported N h) (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ N + 1) :
    (h ⟨n, Finset.mem_Iic.mpr (hnm.trans hm)⟩).1.1 ≤
      (h ⟨m, Finset.mem_Iic.mpr hm⟩).1.1 := by
  induction m with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact le_rfl
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n
      exact le_rfl
    · exact (ih (by omega) (by omega)).trans (hs.clock_lt ⟨m, by omega⟩).le

theorem extractionRun_future_clock_ge (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n m : ℕ) (hn : n < N + 1) (hnm : n ≤ m) (hm : m ≤ N + 1) (k : Fin N)
    (hk : (extractionRun N h n).mergers < k.val)
    (hk' : k.val ≤ (extractionRun N h m).mergers) :
    (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩).1.1 ≤
      ((extractionRun N h m).oldHistory k).1.1 := by
  induction m with
  | zero =>
    have he : n = 0 := by omega
    subst n
    omega
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n
      omega
    · have hnm' : n ≤ m := by omega
      by_cases hkm : k.val ≤ (extractionRun N h m).mergers
      · rw [extractionRun_succ N h m (by omega), extractionStep_history_stable _ _ _ k hkm]
        exact ih hnm' (by omega) hkm
      · rw [extractionRun_succ N h m (by omega)] at hk' ⊢
        obtain ⟨hrecord, hclock⟩ := extractionStep_new_slot _ _ _ k (by omega) hk'
        rw [hrecord, hclock]
        exact hs.clock_mono (n + 1) (m + 1) (by omega) hm

end Rhone.Coalescent.SmcPrime
