/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanClades
public import Rhone.Coalescent.SmcPrimeTreeChronologyMeas
public import Rhone.Coalescent.SmcPrimeKingmanTreeLaw

/-! # Chronology of Kingman metric trees built from histories -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

theorem metric_tree_chronology (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 0 < N) :
    TreeChronology (metricTreeFromHistory N (fun j : Fin N => ω j.val)) := by
  classical
  have hroot := metric_tree_root_height_of_pos N ω hinit hvalid hstep hN
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hfull : (Finset.univ : Finset (Fin N)) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨?_, ?_⟩
  · intro q hq
    by_cases hr : rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) ≤ q
    · simp only [timeClades, hr, ite_true, Finset.mem_singleton]
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        exact hc ▸ hfull
      · intro i
        exact ⟨Finset.univ, rfl, Finset.mem_univ i⟩
      · intro c hc d hd hne
        exact False.elim (hne (hc.trans hd.symm))
    · have hlast : q < (ω (N - 1)).1.1 := by
        rw [← hroot]
        exact lt_of_not_ge hr
      obtain ⟨k, hk, hlo, hhi⟩ := kingman_clock_epoch N ω hinit q hq hlast
      rw [kingman_timeClades_epoch N ω hinit hvalid hstep k hk q hlo hhi]
      exact kingmanSampleClades_partition N ω k
  · intro q r hq hqr c hc
    by_cases hr : rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) ≤ r
    · refine ⟨Finset.univ, ?_, Finset.subset_univ c⟩
      simp only [timeClades, hr, ite_true, Finset.mem_singleton]
    · have hqroot : q < rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) :=
        lt_of_le_of_lt hqr (lt_of_not_ge hr)
      have hrroot : r < rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) :=
        lt_of_not_ge hr
      rw [hroot] at hqroot hrroot
      obtain ⟨k, hk, hklo, hkhi⟩ := kingman_clock_epoch N ω hinit q hq hqroot
      obtain ⟨l, hl, hllo, hlhi⟩ := kingman_clock_epoch N ω hinit r (hq.trans hqr) hrroot
      have hkl : k ≤ l := by
        by_contra hn
        have hclock := hmono (show l + 1 ≤ k by omega)
        exact (not_lt_of_ge ((hclock.trans hklo).trans hqr)) hlhi
      rw [kingman_timeClades_epoch N ω hinit hvalid hstep k hk q hklo hkhi] at hc
      obtain ⟨d, hd, hcd⟩ := kingmanSampleClades_coarsen N ω k l hkl c hc
      refine ⟨d, ?_, hcd⟩
      rw [kingman_timeClades_epoch N ω hinit hvalid hstep l hl r hllo hlhi]
      exact hd

theorem metric_tree_from_history_chronology (N : ℕ) (h : KingmanHistory N)
    (hN : 0 < N) (hs : KingmanHistorySupported N h) :
    TreeChronology (metricTreeFromHistory N h) := by
  have he : (fun j : Fin N => kingmanCompletion N h j.val) = h := by
    funext j
    exact kingmanCompletion_prefix N h j.val j.isLt
  have hc := metric_tree_chronology N (kingmanCompletion N h)
    hs.completion_init hs.completion_valid hs.completion_step hN
  rw [he] at hc
  exact hc

theorem kingmanHistoryLaw_tree_chronology (N : ℕ) (hN : 0 < N) :
    ∀ᵐ h ∂kingmanHistoryLaw N, TreeChronology (metricTreeFromHistory N h) := by
  filter_upwards [kingmanHistoryLaw_supported N] with h hs
  exact metric_tree_from_history_chronology N h hN hs

theorem kingmanTreeLaw_chronology (N : ℕ) (hN : 0 < N) :
    ∀ᵐ T ∂kingmanTreeLaw N, TreeChronology T := by
  unfold kingmanTreeLaw
  exact (ae_map_iff (metricTreeFromHistory_measurable N).aemeasurable
    (TreeChronology_measurable N)).mpr (kingmanHistoryLaw_tree_chronology N hN)

end Rhone.Coalescent.SmcPrime
