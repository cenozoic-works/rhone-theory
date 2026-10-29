/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitHistoryPersistence

/-! # Old ancestor labels along the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem oldAncestor_of_history_stable {N : ℕ} {z z' : OneSplitExtractionState N}
    (h : ExtractedHistoryPrefix N z)
    (hs : ∀ k : Fin N, k.val ≤ z.mergers → z'.oldHistory k = z.oldHistory k)
    (a : Fin N) :
    ancestorLabel N (historyExtension N z'.oldHistory) leftBoundaryProbe a z.mergers =
      ancestorLabel N (historyExtension N z.oldHistory) leftBoundaryProbe a z.mergers := by
  apply ancestorLabel_eq_of_prefix
  intro l hl
  have hlN : l < N := hl.trans_lt h.bound
  simp only [historyExtension, dite_eq_left hlN]
  exact hs ⟨l, hlN⟩ hl

theorem oldLabels_of_history_step {N : ℕ} {z z' : OneSplitExtractionState N}
    (h : ExtractedHistoryPrefix N z) (h' : ExtractedHistoryPrefix N z')
    (hs : ∀ k : Fin N, k.val ≤ z.mergers → z'.oldHistory k = z.oldHistory k)
    (hg : ∀ a, z.oldLabels a =
      ancestorLabel N (historyExtension N z.oldHistory) leftBoundaryProbe a z.mergers)
    (he : (z'.mergers = z.mergers ∧ z'.oldLabels = z.oldLabels) ∨
      (z'.mergers = z.mergers + 1 ∧ z'.oldLabels =
        fun a => ancestorStep z.old.1 z'.old.2.2 leftBoundaryProbe (z.oldLabels a))) :
    ∀ a, z'.oldLabels a =
      ancestorLabel N (historyExtension N z'.oldHistory) leftBoundaryProbe a z'.mergers := by
  intro a
  have hanc := oldAncestor_of_history_stable h hs a
  rcases he with ⟨hm, hf⟩ | ⟨hm, hf⟩
  · rw [hm, hf, hanc]
    exact hg a
  · have hb : z.mergers + 1 < N := by rw [← hm]; exact h'.bound
    have hpre : historyExtension N z'.oldHistory z.mergers = z.old := by
      simp only [historyExtension, dite_eq_left h.bound]
      rw [hs ⟨z.mergers, h.bound⟩ le_rfl, h.current]
    have hnext : historyExtension N z'.oldHistory (z.mergers + 1) = z'.old := by
      simp only [historyExtension, dite_eq_left hb]
      have hi : (⟨z.mergers + 1, hb⟩ : Fin N) = ⟨z'.mergers, h'.bound⟩ := Fin.ext hm.symm
      rw [hi, h'.current]
    rw [hm, hf, ancestorLabel, hpre, hnext, hanc, ← hg a]

theorem extractionStep_old_labels_evolution {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (h : ExtractionInventory z pre.1) (hs : Valid pre.1)
    (ht : ARGTransition (pre, next)) (he : next.2.2 ∈ coalSet ∨ next.2.2 ∈ splitSet) :
    ((extractionStep z pre next).mergers = z.mergers ∧
      (extractionStep z pre next).oldLabels = z.oldLabels) ∨
    ((extractionStep z pre next).mergers = z.mergers + 1 ∧
      (extractionStep z pre next).oldLabels = fun a =>
        ancestorStep z.old.1 (extractionStep z pre next).old.2.2
          leftBoundaryProbe (z.oldLabels a)) := by
  classical
  rcases he with he | he
  · obtain ⟨i, j, hij, hev, _, _⟩ := ht.coal_case he
    have hiuid : liveLabelAt pre.1 i.val = (pre.1.2.2.2 i).1 := by
      simp only [liveLabelAt, dite_eq_left i.isLt]
    have hjuid : liveLabelAt pre.1 j.val = (pre.1.2.2.2 j).1 := by
      simp only [liveLabelAt, dite_eq_left j.isLt]
    by_cases hd : ∃ d, z.detached = some d ∧
        (d = (pre.1.2.2.2 i).1 ∨ d = (pre.1.2.2.2 j).1)
    · left
      simp only [extractionStep, hev, hiuid, hjuid, ite_eq_left hd]
      exact ⟨True.intro, True.intro⟩
    · have hi : z.detached ≠ some (pre.1.2.2.2 i).1 := by
        intro hh
        exact hd ⟨_, hh, Or.inl rfl⟩
      have hj : z.detached ≠ some (pre.1.2.2.2 j).1 := by
        intro hh
        exact hd ⟨_, hh, Or.inr rfl⟩
      obtain ⟨p, q, _, hold, hgold⟩ :=
        extractionStep_old_pair z pre next h hs i j hij hev hi hj
      right
      constructor
      · simp only [extractionStep, hev, hiuid, hjuid, ite_eq_right hd]
      · rw [hold]
        exact hgold
  · obtain ⟨i, x, _, _, hev, _, _⟩ := ht.split_case hs he
    left
    simp only [extractionStep, hev]
    exact ⟨True.intro, True.intro⟩

theorem extractionRun_old_labels (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n ≤ N + 1) (a : Fin N) :
    (extractionRun N h n).oldLabels a =
      ancestorLabel N (historyExtension N (extractionRun N h n).oldHistory)
        leftBoundaryProbe a (extractionRun N h n).mergers := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hlt : n < N + 1 := by omega
    let k : Fin (N + 1) := ⟨n, hlt⟩
    have he : (h ⟨n + 1, Finset.mem_Iic.mpr hn⟩).2.2 ∈ coalSet ∨
        (h ⟨n + 1, Finset.mem_Iic.mpr hn⟩).2.2 ∈ splitSet := by
      obtain ⟨s, hsplit, hcoal⟩ := hs.2.2.2.2.1
      by_cases hk : k = s
      · right
        simpa only [← hk] using hsplit
      · exact Or.inl (hcoal k hk)
    have hh' := extractionRun_history_prefix N h hs (n + 1) hn
    rw [extractionRun_succ N h n hlt] at hh' ⊢
    apply oldLabels_of_history_step (extractionRun_history_prefix N h hs n (by omega)) hh'
      (fun b hb => extractionStep_history_stable _ _ _ b hb)
      (fun b => ih (by omega) b)
    exact extractionStep_old_labels_evolution _ _ _
      (extractionRun_inventory N h hs n (by omega)) (hs.2.1 _)
      (hs.2.2.1 k) he

theorem extractionRun_final_old_labels (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n ≤ N + 1) (a : Fin N) :
    (extractionRun N h n).oldLabels a =
      ancestorLabel N (historyExtension N (extractOneSplitSkeleton N h).1)
        leftBoundaryProbe a (extractionRun N h n).mergers := by
  change _ = ancestorLabel N
    (historyExtension N (extractionRun N h (N + 1)).oldHistory)
    leftBoundaryProbe a (extractionRun N h n).mergers
  rw [oldAncestor_of_history_stable (extractionRun_history_prefix N h hs n hn)
    (fun k hk => extractionRun_history_stable N h n (N + 1) hn le_rfl k hk)]
  exact extractionRun_old_labels N h hs n hn a

end Rhone.Coalescent.SmcPrime
