/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExposureSupport
public import Rhone.Coalescent.SmcPrimeExposureDomination
public import Rhone.Coalescent.SmcPrimeOneSplitCarrierSupport

/-! # Hull exposure of the one-split ARG prefix dominates both extracted tree lengths -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport
attribute [local instance] Classical.propDecidable

theorem extractOneSplitSkeleton_hull_exposure (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    let η := extractOneSplitSkeleton N h
    let ω := extractionPrefixExtension N h
    η.2.2.2.1 * treeLength (metricTreeFromHistory N η.1) +
      (1 - η.2.2.2.1) * treeLength (oneSplitPostTree η) ≤
      argHullExposure (fun k : Fin (N + 1) => (ω k.val).1)
        (fun k => (ω (k.val + 1)).1.1 - (ω k.val).1.1) := by
  classical
  dsimp only
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  let η := extractOneSplitSkeleton N h
  let ω := extractionPrefixExtension N h
  let τ : ℕ → ℝ := fun k => (h ⟨min k (N + 1), Finset.mem_Iic.mpr (Nat.min_le_right _ _)⟩).1.1
  have hτ (k : ℕ) (hk : k ≤ N + 1) : τ k = (ω k).1.1 := by
    simp only [τ, Nat.min_eq_left hk, ω, extractionPrefixExtension_prefix N h k hk]
  have hzero : τ 0 = 0 := by simp [τ, hs.1, initialState]
  have hmono : Monotone τ := by
    intro k l hkl
    exact hs.clock_mono _ _ (by omega) (Nat.min_le_right _ _)
  have hcoords := extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
    w.cutPosition w.cut_event w.other_event
  have hx : η.2.2.2.1 = w.cutPosition := hcoords.2
  have hr := extractOneSplitSkeleton_root_bounds N h hs
  have hroots : rootHeight (metricTreeFromHistory N η.1) ≤ τ (N + 1) ∧
      rootHeight (oneSplitPostTree η) ≤ τ (N + 1) := by
    simpa only [τ, Nat.min_self] using hr
  have hk := extractOneSplitSkeleton_history_supported N h hs
  have hnonneg := metric_tree_from_history_nonnegative N η.1 (fun k => (hk.1 k).1.1)
  have huni := metric_tree_from_history_active_unique N η.1 hs.sample_pos hk
  have hpost := extractOneSplitSkeleton_post_geometry N h hs
  have hreach (k : ℕ) (hk : k < N + 1) :
      ZeroSplitReachable (ω k).1 ∨ OneSplitReachable w.cutPosition (ω k).1 := by
    have he := oneSplitPrefix_reachable N h hs w.cutStep w.cutIndex w.cutPosition
      w.cut_event k hk.le
    by_cases hc : k ≤ w.cutStep.val
    · exact Or.inl (by simpa only [hc, ite_true] using he)
    · exact Or.inr (by simpa only [hc, ite_false] using he)
  obtain ⟨q, hqx, hq1⟩ := exists_rat_btwn w.cut_lt_one
  let q' : GenomicProbe := ⟨q, by exact_mod_cast (w.cut_pos.le.trans hqx.le),
    by exact_mod_cast hq1⟩
  have hprobe : η.2.2.2.1 ≤ (q'.val : ℝ) := hx.trans_le hqx.le
  have hbound := argHullExposure_ge_tree_lengths
    (metricTreeFromHistory N η.1) (oneSplitPostTree η) hnonneg hpost.2.1 w.cutPosition
    w.cut_pos w.cut_lt_one (fun k => (ω k).1) τ hzero hmono hroots.1 hroots.2 hreach
  have htime (k : ℕ) (hk : k < N + 1) (y : ℝ)
      (hy : y ∈ Set.Ioo (τ k) (τ (k + 1))) :
      0 ≤ y ∧ (ω k).1.1 ≤ y ∧ y < (ω (k + 1)).1.1 := by
    have ht : 0 ≤ τ k := by
      exact hs.clock_nonneg _
    refine ⟨ht.trans hy.1.le, ?_, ?_⟩
    · simpa only [hτ k hk.le] using hy.1.le
    · simpa only [hτ (k + 1) hk] using hy.2
  have hleft : ∀ k < N + 1, ∀ y ∈ Set.Ioo (τ k) (τ (k + 1)),
      attachmentRate (metricTreeFromHistory N η.1) y ≤
        ∑ i, if materialContains ((ω k).1.2.2.2 i).2 0 then (1 : ℝ) else 0 := by
    intro k hk y hy
    obtain ⟨hy0, hlo, hhi⟩ := htime k hk y hy
    apply attachment_rate_le_carrier_sum hs.sample_pos _ huni y hy0 (ω k).1 0
      (fun j => ancestorLabel N ω leftBoundaryProbe j k)
    · intro j
      simpa only [leftBoundaryProbe, Rat.cast_zero] using
        oneSplitPrefix_ancestorCarried N h hs leftBoundaryProbe j k hk.le
    · intro b hb
      have hmem := branch_active_time_clade (metricTreeFromHistory N η.1) y b
        (Finset.mem_filter.mp hb).2
      rw [extraction_timeClades_epoch_labels N h hs k hk y hlo hhi] at hmem
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      exact ⟨ancestorLabel N ω leftBoundaryProbe j k, hj.symm⟩
  have hright : ∀ k < N + 1, ∀ y ∈ Set.Ioo (τ k) (τ (k + 1)),
      attachmentRate (oneSplitPostTree η) y ≤
        ∑ i, if materialContains ((ω k).1.2.2.2 i).2 w.cutPosition then (1 : ℝ) else 0 := by
    intro k hk y hy
    obtain ⟨hy0, hlo, hhi⟩ := htime k hk y hy
    apply attachment_rate_le_carrier_sum hs.sample_pos _ hpost.2.2.2 y hy0 (ω k).1
      w.cutPosition (fun j => ancestorLabel N ω q' j k)
    · intro j
      obtain ⟨i, hi, hmat⟩ := oneSplitPrefix_ancestorCarried N h hs q' j k hk.le
      exact ⟨i, hi, (reachable_right_carrier_iff w.cutPosition w.cut_pos w.cut_lt_one
        (ω k).1 (hreach k hk) q hqx.le hq1 i).mp hmat⟩
    · exact extractOneSplitSkeleton_right_active_clade N h hs q' hprobe k hk y hlo hhi
  have he := hbound hleft hright
  rw [← hx] at he
  convert he using 1
  unfold argHullExposure
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  rw [hτ (k.val + 1) k.isLt, hτ k.val k.isLt.le]

end Rhone.Coalescent.SmcPrime
