/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitCoalEpoch

/-! # Total pair exposure splits into old-tree exposure and detached-lineage exposure -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
theorem argPrefix_sum_integrals (N : ℕ) (h : ARGPrefix (N + 1)) (f : ℝ → ℝ)
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∑ k : Fin (N + 1), ∫ q in (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1..
      (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1, f q) =
      ∫ q in (h ⟨0, Finset.mem_Iic.mpr (by omega)⟩).1.1..
        (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1, f q := by
  let a : ℕ → ℝ := fun k => (extractionPrefixExtension N h k).1.1
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (n := N + 1) (fun k _ => hf (a k) (a (k + 1)))
  rw [← Fin.sum_univ_eq_sum_range] at he
  dsimp only [a] at he
  rw [extractionPrefixExtension_prefix N h 0 (by omega),
    extractionPrefixExtension_prefix N h (N + 1) le_rfl] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro k _
  rw [extractionPrefixExtension_prefix N h k.val (by omega),
    extractionPrefixExtension_prefix N h (k.val + 1) k.isLt]

theorem oneSplitCoalExposure_eq (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    argCoalExposure
      (fun k : Fin (N + 1) => (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1)
      (fun k : Fin (N + 1) =>
        (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1 -
        (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1) =
      oldCoalExposure N (extractOneSplitSkeleton N h).1 +
        attachmentHazard (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
          (extractOneSplitSkeleton N h).2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.1 := by
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  let η := extractOneSplitSkeleton N h
  let T := metricTreeFromHistory N η.1
  let t := η.2.2.1
  let U := η.2.2.2.2.1
  let b := (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.1
  have hzero : (h ⟨0, Finset.mem_Iic.mpr (by omega)⟩).1.1 = 0 := by rw [hs.1]; rfl
  have he : argCoalExposure
      (fun k : Fin (N + 1) => (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1)
      (fun k : Fin (N + 1) =>
        (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1 -
        (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1) =
    (∑ k : Fin (N + 1), ∫ q in (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1..
      (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1, oldTreeCoalRate T q) +
    (∑ k : Fin (N + 1), ∫ q in (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1..
      (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1, detachedAttachmentRate T t U q) := by
    unfold argCoalExposure
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [extractionRun_old_pair_integral N h hs k,
      extractionRun_detached_integral N h hs w k,
      (extractionRun_inventory N h hs k.val (by omega)).arg_pair_rate (hs.2.1 _),
      add_mul]
  rw [he, argPrefix_sum_integrals N h _ (oldTreeCoalRate_intervalIntegrable T),
    argPrefix_sum_integrals N h _ (detachedAttachmentRate_intervalIntegrable T t U), hzero]
  have ht : 0 ≤ t := by
    dsimp only [t, η]
    rw [w.cut_time]
    exact hs.clock_nonneg _
  have htU : t ≤ U := by
    dsimp only [t, U, η]
    rw [w.cut_time, w.attach_time]
    exact hs.clock_mono _ _ (by have := w.cut_before_attach; omega) w.attach_bound
  have hUb : U ≤ b := by
    dsimp only [U, η, b]
    rw [w.attach_time]
    exact hs.clock_mono _ _ (by have := w.attach_bound; omega) le_rfl
  rw [oldCoalExposure_integral N η.1 hs.sample_pos
      (extractOneSplitSkeleton_history_supported N h hs) b
      (extractOneSplitSkeleton_root_bounds N h hs).1,
    detachedAttachmentRate_integral T t U b ht htU hUb]
end Rhone.Coalescent.SmcPrime
