/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitOldLabels
public import Rhone.Coalescent.SmcPrimeOneSplitFutureClock

/-! # Time clades and root labels over the epochs of the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ExtractionInventory.old_root_labels {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (hc : z.old.1.2.2.1 = 1)
    (a b : Fin N) : z.argLabels a = z.argLabels b := by
  obtain ⟨i, hi⟩ := h.2.2.1 a
  obtain ⟨j, hj⟩ := h.2.2.1 b
  have he : i = j := by
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  apply (h.2.2.2.2 a b).mpr
  exact hi.symm.trans ((congrArg (fun k => (z.old.1.2.2.2 k).1) he).trans hj)

theorem extraction_timeClades_epoch (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (hn : n < N + 1) (q : ℝ)
    (hlo : (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.1 ≤ q)
    (hhi : q < (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩).1.1) :
    timeClades (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) q =
      Finset.univ.image (fun a => extractionClade (extractionRun N h n).argLabels
        ((extractionRun N h n).argLabels a)) := by
  classical
  let z := extractionRun N h n
  let η := extractOneSplitSkeleton N h
  let ω := kingmanCompletion N η.1
  have hp := extractionRun_history_prefix N h hs n (by omega)
  have hsη := extractOneSplitSkeleton_history_supported N h hs
  have he : (fun j : Fin N => ω j.val) = η.1 := by
    funext j
    exact kingmanCompletion_prefix N η.1 j.val j.isLt
  have hcur : η.1 ⟨z.mergers, hp.bound⟩ = z.old := by
    change (extractionRun N h (N + 1)).oldHistory ⟨z.mergers, hp.bound⟩ = z.old
    rw [extractionRun_history_stable N h n (N + 1) (by omega) le_rfl _ le_rfl]
    exact hp.current
  have hl : (ω z.mergers).1.1 ≤ q := by
    dsimp only [ω]
    rw [kingmanCompletion_prefix N η.1 z.mergers hp.bound, hcur]
    exact (extractionRun_clock_le N h hs n (by omega)).trans hlo
  have hlabels (a : Fin N) : ancestorLabel N ω leftBoundaryProbe a z.mergers =
      z.oldLabels a := by
    have hprefix : ∀ l, l ≤ z.mergers → ω l = historyExtension N η.1 l := by
      intro l hll
      have hlN : l < N := hll.trans_lt hp.bound
      simp only [ω, kingmanCompletion_prefix N η.1 l hlN,
        historyExtension, dite_eq_left hlN]
    rw [ancestorLabel_eq_of_prefix N ω (historyExtension N η.1)
      leftBoundaryProbe a z.mergers hprefix]
    exact (extractionRun_final_old_labels N h hs n (by omega) a).symm
  by_cases hm : z.mergers < N - 1
  · have hu : q < (ω (z.mergers + 1)).1.1 := by
      have hb : z.mergers + 1 < N := by omega
      dsimp only [ω]
      rw [kingmanCompletion_prefix N η.1 (z.mergers + 1) hb]
      apply hhi.trans_le
      exact extractionRun_future_clock_ge N h hs n (N + 1) hn (by omega) le_rfl
        ⟨z.mergers + 1, hb⟩ (by dsimp only [z]; omega)
        (by rw [extractionRun_final_mergers N h hs]; change z.mergers + 1 ≤ N - 1; omega)
    have ht := kingman_timeClades_epoch N ω hsη.completion_init hsη.completion_valid
      hsη.completion_step z.mergers hm q hl hu
    rw [he] at ht
    rw [ht]
    unfold kingmanSampleClades
    apply Finset.image_congr
    intro a _
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, extractionClade, hlabels]
    exact (extractionRun_inventory N h hs n (by omega)).2.2.2.2 b a |>.symm
  · have hm' : z.mergers = N - 1 := by have hb : z.mergers < N := hp.bound; omega
    have hr := metric_tree_root_height_of_pos N ω hsη.completion_init
      hsη.completion_valid hsη.completion_step hs.sample_pos
    rw [he] at hr
    have hrq : rootHeight (metricTreeFromHistory N η.1) ≤ q := by
      rw [hr, ← hm']
      exact hl
    rw [show timeClades (metricTreeFromHistory N η.1) q = {Finset.univ} by
      simp only [timeClades, hrq, ite_true]]
    have hc : z.old.1.2.2.1 = 1 := by
      have hh := (hp.records ⟨z.mergers, hp.bound⟩ le_rfl).2
      rw [hp.current] at hh
      change z.old.1.2.2.1 = N - z.mergers at hh
      have := hs.sample_pos
      omega
    have hphys := extractionRun_inventory N h hs n (by omega)
    have hf (a : Fin N) : extractionClade z.argLabels (z.argLabels a) =
        Finset.univ := by
      ext b
      simp only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (hphys.old_root_labels hc b a)
    ext c
    simp only [Finset.mem_singleton, Finset.mem_image]
    constructor
    · intro hc
      exact ⟨⟨0, hs.sample_pos⟩, Finset.mem_univ _, (hf _).trans hc.symm⟩
    · rintro ⟨a, _, ha⟩
      exact ha.symm.trans (hf a)

theorem extraction_timeClades_terminal (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (q : ℝ) (hq : (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1 ≤ q) :
    timeClades (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) q =
      Finset.univ.image (fun a =>
        extractionClade (extractionRun N h (N + 1)).argLabels
          ((extractionRun N h (N + 1)).argLabels a)) := by
  classical
  let z := extractionRun N h (N + 1)
  let η := extractOneSplitSkeleton N h
  let ω := kingmanCompletion N η.1
  have hp := extractionRun_history_prefix N h hs (N + 1) le_rfl
  have hsη := extractOneSplitSkeleton_history_supported N h hs
  have he : (fun j : Fin N => ω j.val) = η.1 := by
    funext j
    exact kingmanCompletion_prefix N η.1 j.val j.isLt
  have hm : z.mergers = N - 1 := extractionRun_final_mergers N h hs
  have hb : N - 1 < N := by have := hs.sample_pos; omega
  have hcur : η.1 ⟨N - 1, hb⟩ = z.old := by
    have hi : (⟨N - 1, hb⟩ : Fin N) = ⟨z.mergers, hp.bound⟩ := Fin.ext hm.symm
    rw [hi]
    exact hp.current
  have hr := metric_tree_root_height_of_pos N ω hsη.completion_init
    hsη.completion_valid hsη.completion_step hs.sample_pos
  rw [he] at hr
  dsimp only [ω] at hr
  rw [kingmanCompletion_prefix N η.1 (N - 1) hb, hcur] at hr
  have hrq : rootHeight (metricTreeFromHistory N η.1) ≤ q := by
    rw [hr]
    exact (extractionRun_clock_le N h hs (N + 1) le_rfl).trans hq
  rw [show timeClades (metricTreeFromHistory N η.1) q = {Finset.univ} by
    simp only [timeClades, hrq, ite_true]]
  have hc : z.old.1.2.2.1 = 1 := (extractionRun_terminal_inventory N h hs).2
  have hphys := extractionRun_inventory N h hs (N + 1) le_rfl
  have hf (a : Fin N) : extractionClade z.argLabels (z.argLabels a) =
      Finset.univ := by
    ext b
    simp only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (hphys.old_root_labels hc b a)
  ext c
  simp only [Finset.mem_singleton, Finset.mem_image]
  constructor
  · intro hc
    exact ⟨⟨0, hs.sample_pos⟩, Finset.mem_univ _, (hf _).trans hc.symm⟩
  · rintro ⟨a, _, ha⟩
    exact ha.symm.trans (hf a)

theorem OneSplitPrefixSupported.clock_nonneg {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)}
    (hs : OneSplitPrefixSupported N h) (k : Finset.Iic (N + 1)) : 0 ≤ (h k).1.1 :=
  (hs.2.1 k).1

end Rhone.Coalescent.SmcPrime
