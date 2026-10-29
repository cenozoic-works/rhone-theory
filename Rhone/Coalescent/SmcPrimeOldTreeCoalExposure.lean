/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeKingmanObservation
public import Rhone.Coalescent.SmcPrimeKingmanLength
public import Rhone.Coalescent.SmcSupport.ARGClockProduct

/-! # Old-tree pair coalescence exposure and detached attachment-rate integrals -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
noncomputable def oldCoalExposure (N : ℕ) (h : KingmanHistory N) : ℝ :=
  ∑ k : Fin (N - 1), ((N - k.val : ℕ) : ℝ) * (((N - k.val : ℕ) : ℝ) - 1) / 2 *
    ((h ⟨k.val + 1, by omega⟩).1.1 - (h ⟨k.val, by omega⟩).1.1)

theorem oldCoalExposure_measurable (N : ℕ) : Measurable (oldCoalExposure N) := by
  apply Finset.measurable_sum Finset.univ
  intro k _
  exact measurable_const.mul
    ((measurable_pi_apply (⟨k.val + 1, by omega⟩ : Fin N)).fst.fst.sub
      (measurable_pi_apply (⟨k.val, by omega⟩ : Fin N)).fst.fst)

theorem oldCoalExposure_eq_argCoalExposure (N : ℕ) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h) :
    oldCoalExposure N h = argCoalExposure
      (fun k : Fin (N - 1) => (h ⟨k.val, by omega⟩).1)
      (fun k : Fin (N - 1) =>
        (h ⟨k.val + 1, by omega⟩).1.1 - (h ⟨k.val, by omega⟩).1.1) := by
  unfold oldCoalExposure argCoalExposure
  apply Finset.sum_congr rfl
  intro k _
  have hc := (hs.1 (⟨k.val, by omega⟩ : Fin N)).2
  rw [hc]

theorem oldCoalExposure_eq_rate_zero (N : ℕ) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h) :
    oldCoalExposure N h =
      ∑ k : Fin (N - 1), (totalRate false 0 (h ⟨k.val, by omega⟩).1 : ℝ) *
        ((h ⟨k.val + 1, by omega⟩).1.1 - (h ⟨k.val, by omega⟩).1.1) := by
  rw [oldCoalExposure_eq_argCoalExposure N h hs]
  unfold argCoalExposure
  apply Finset.sum_congr rfl
  intro k _
  rw [totalRate_unrestricted_real 0 (by positivity)]
  simp [recombinationRate]

noncomputable def oldTreeCoalRate {N : ℕ} (T : Tree N) (q : ℝ) : ℝ :=
  attachmentRate T q * (attachmentRate T q - 1) / 2

theorem oldTreeCoalRate_measurable {N : ℕ} (T : Tree N) : Measurable (oldTreeCoalRate T) :=
  ((measurable_attachmentRate T).mul
    ((measurable_attachmentRate T).sub measurable_const)).div_const 2

theorem attachmentRate_le_branch_count {N : ℕ} (T : Tree N) (q : ℝ) :
    attachmentRate T q ≤ (T.1 : ℝ) + 1 := by
  unfold attachmentRate
  split_ifs
  · have hn : (0 : ℝ) ≤ T.1 := Nat.cast_nonneg _
    linarith
  · have h := Finset.card_le_univ (activeBranches T q)
    simp only [Fintype.card_fin] at h
    have hc : ((activeBranches T q).card : ℝ) ≤ T.1 := by exact_mod_cast h
    linarith

theorem oldTreeCoalRate_intervalIntegrable {N : ℕ} (T : Tree N) (a b : ℝ) :
    IntervalIntegrable (oldTreeCoalRate T) volume a b := by
  let M : ℝ := (T.1 : ℝ) + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (q : ℝ) : ‖oldTreeCoalRate T q‖ ≤ M * (M + 1) / 2 := by
    have hn := attachmentRate_nonneg T q
    have hnM : attachmentRate T q ≤ M := attachmentRate_le_branch_count T q
    have ha : |attachmentRate T q - 1| ≤ M + 1 := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg hn, abs_one]
      linarith
    unfold oldTreeCoalRate
    rw [norm_div, norm_mul, Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs]
    norm_num only [Real.norm_ofNat]
    exact div_le_div_of_nonneg_right (mul_le_mul hnM ha (abs_nonneg _) hM) (by norm_num)
  let : IsFiniteMeasure (volume.restrict (Set.uIcc a b)) := by
    change IsFiniteMeasure (volume.restrict (Set.Icc (min a b) (max a b)))
    infer_instance
  have hi : IntegrableOn (oldTreeCoalRate T) (Set.uIcc a b) :=
    Integrable.of_bound (oldTreeCoalRate_measurable T).aestronglyMeasurable _
      (Filter.Eventually.of_forall hb)
  exact hi.intervalIntegrable

theorem oldTreeCoalRate_after_root {N : ℕ} (T : Tree N) (q : ℝ)
    (hq : rootHeight T ≤ q) : oldTreeCoalRate T q = 0 := by
  simp [oldTreeCoalRate, attachmentRate, hq]

theorem oldCoalExposure_integral_root (N : ℕ) (h : KingmanHistory N)
    (hN : 1 ≤ N) (hs : KingmanHistorySupported N h) :
    (∫ q in (0 : ℝ)..rootHeight (metricTreeFromHistory N h),
      oldTreeCoalRate (metricTreeFromHistory N h) q) = oldCoalExposure N h := by
  let ω := kingmanCompletion N h
  let T := metricTreeFromHistory N h
  have he : (fun j : Fin N => ω j.val) = h := by
    funext j
    exact kingmanCompletion_prefix N h j.val j.isLt
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hs.completion_step k).time_le)
  have hroot := metric_tree_root_height_of_pos N ω hs.completion_init
    hs.completion_valid hs.completion_step (by omega)
  rw [he] at hroot
  have hzero : (ω 0).1.1 = 0 := by rw [hs.completion_init]; rfl
  rw [hroot, ← hzero,
    ← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => oldTreeCoalRate_intervalIntegrable T (ω k).1.1 (ω (k + 1)).1.1),
    ← Fin.sum_univ_eq_sum_range, oldCoalExposure_eq_argCoalExposure N h hs]
  unfold argCoalExposure
  apply Finset.sum_congr rfl
  intro k _
  have hi : (∫ q in (ω k.val).1.1..(ω (k.val + 1)).1.1, oldTreeCoalRate T q) =
      ∫ _q in (ω k.val).1.1..(ω (k.val + 1)).1.1,
        ((ω k.val).1.2.2.1 : ℝ) * (((ω k.val).1.2.2.1 : ℝ) - 1) / 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (ω (k.val + 1)).1.1] with q hneq hmem
    rw [Set.uIoc_of_le (hmono (Nat.le_succ k.val))] at hmem
    have hhi : q < (ω (k.val + 1)).1.1 := lt_of_le_of_ne hmem.2 hneq
    have hqr : q < rootHeight T := by
      rw [hroot]
      exact hhi.trans_le (hmono (by have := k.isLt; omega))
    have ha := kingman_active_branch_card N ω hs.completion_init hs.completion_valid
      hs.completion_step k.val k.isLt q hmem.1.le hhi
    rw [he] at ha
    change (activeBranches T q).card = _ at ha
    simp only [oldTreeCoalRate, attachmentRate, not_le.mpr hqr, ite_false, ha]
  rw [hi, intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  dsimp only [ω]
  rw [
    kingmanCompletion_prefix N h k.val (by omega),
    kingmanCompletion_prefix N h (k.val + 1) (by omega)]

theorem oldCoalExposure_integral (N : ℕ) (h : KingmanHistory N)
    (hN : 1 ≤ N) (hs : KingmanHistorySupported N h) (b : ℝ)
    (hb : rootHeight (metricTreeFromHistory N h) ≤ b) :
    (∫ q in (0 : ℝ)..b, oldTreeCoalRate (metricTreeFromHistory N h) q) =
      oldCoalExposure N h := by
  let T := metricTreeFromHistory N h
  have hz : (∫ q in rootHeight T..b, oldTreeCoalRate T q) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with q hq
    rw [Set.uIoc_of_le hb] at hq
    exact oldTreeCoalRate_after_root T q hq.1.le
  have he := intervalIntegral.integral_add_adjacent_intervals
    (oldTreeCoalRate_intervalIntegrable T 0 (rootHeight T))
    (oldTreeCoalRate_intervalIntegrable T (rootHeight T) b)
  rw [oldCoalExposure_integral_root N h hN hs, hz, add_zero] at he
  exact he.symm

noncomputable def detachedAttachmentRate {N : ℕ} (T : Tree N) (t U q : ℝ) : ℝ :=
  (Set.Ioo t U).indicator (attachmentRate T) q

theorem detachedAttachmentRate_intervalIntegrable {N : ℕ} (T : Tree N) (t U a b : ℝ) :
    IntervalIntegrable (detachedAttachmentRate T t U) volume a b :=
  intervalIntegrable_iff.mpr
    ((attachmentRate_intervalIntegrable T a b).def'.indicator measurableSet_Ioo)

theorem detachedAttachmentRate_integral {N : ℕ} (T : Tree N) (t U b : ℝ)
    (ht : 0 ≤ t) (htU : t ≤ U) (hUb : U ≤ b) :
    (∫ q in (0 : ℝ)..b, detachedAttachmentRate T t U q) = attachmentHazard T t U := by
  have hfirst : (∫ q in (0 : ℝ)..t, detachedAttachmentRate T t U q) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with q hq
    rw [Set.uIoc_of_le ht] at hq
    simp [detachedAttachmentRate, Set.mem_Ioo, not_lt.mpr hq.2]
  have hlast : (∫ q in U..b, detachedAttachmentRate T t U q) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with q hq
    rw [Set.uIoc_of_le hUb] at hq
    simp [detachedAttachmentRate, Set.mem_Ioo, not_lt.mpr hq.1.le]
  have hmid : (∫ q in t..U, detachedAttachmentRate T t U q) = attachmentHazard T t U := by
    apply intervalIntegral.integral_congr_Ioo_of_le htU
    intro q hq
    simp [detachedAttachmentRate, hq]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (detachedAttachmentRate_intervalIntegrable T t U 0 t)
    (detachedAttachmentRate_intervalIntegrable T t U t U)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (detachedAttachmentRate_intervalIntegrable T t U 0 U)
    (detachedAttachmentRate_intervalIntegrable T t U U b)
  rw [hfirst, hmid, zero_add] at h1
  rw [← h1, hlast, add_zero] at h2
  exact h2.symm
end Rhone.Coalescent.SmcPrime
