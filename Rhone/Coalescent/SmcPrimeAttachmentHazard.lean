/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeAttachmentIntervals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Cumulative attachment hazard of the old tree between finite boundaries

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–6. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess Filter

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
noncomputable def attachmentHazard {N : ℕ} (T : Tree N) (t x : ℝ) : ℝ :=
  ∫ s in t..x, attachmentRate T s

theorem measurable_attachmentRate {N : ℕ} (T : Tree N) :
    Measurable (attachmentRate T) :=
  (attachmentRateFiber_measurable N T.1).comp (measurable_const.prodMk measurable_id)

theorem attachmentRate_nonneg {N : ℕ} (T : Tree N) (s : ℝ) :
    0 ≤ attachmentRate T s := by
  unfold attachmentRate
  split_ifs <;> positivity

theorem attachmentRate_intervalIntegrable {N : ℕ} (T : Tree N) (a b : ℝ) :
    IntervalIntegrable (attachmentRate T) volume a b := by
  have hb : ∀ s, ‖attachmentRate T s‖ ≤ (T.1 : ℝ) + 1 := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (attachmentRate_nonneg T s)]
    unfold attachmentRate
    split_ifs
    · have h : (0 : ℝ) ≤ T.1 := Nat.cast_nonneg _
      linarith
    · have h := Finset.card_le_univ (activeBranches T s)
      simp only [Fintype.card_fin] at h
      have hc : ((activeBranches T s).card : ℝ) ≤ T.1 := by exact_mod_cast h
      linarith
  let : IsFiniteMeasure (volume.restrict (Set.uIcc a b)) := by
    change IsFiniteMeasure (volume.restrict (Set.Icc (min a b) (max a b)))
    infer_instance
  have hi : IntegrableOn (attachmentRate T) (Set.uIcc a b) :=
    Integrable.of_bound (measurable_attachmentRate T).aestronglyMeasurable _
      (Eventually.of_forall hb)
  exact hi.intervalIntegrable

theorem attachmentHazard_nonneg {N : ℕ} (T : Tree N) (t x : ℝ) (hx : t ≤ x) :
    0 ≤ attachmentHazard T t x :=
  intervalIntegral.integral_nonneg hx (fun _ _ => attachmentRate_nonneg T _)

theorem attachmentHazard_add {N : ℕ} (T : Tree N) (t s x : ℝ) :
    attachmentHazard T t s + attachmentHazard T s x = attachmentHazard T t x :=
  intervalIntegral.integral_add_adjacent_intervals
    (attachmentRate_intervalIntegrable T t s) (attachmentRate_intervalIntegrable T s x)

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
theorem attachmentHazard_above_root {N : ℕ} (T : Tree N) (t x : ℝ)
    (ht : rootHeight T ≤ t) (hx : t ≤ x) : attachmentHazard T t x = x - t := by
  unfold attachmentHazard
  rw [intervalIntegral.integral_congr_Ioo_of_le hx
    (g := fun _ => (1 : ℝ)) (fun s hs => by
      simp [attachmentRate, ht.trans hs.1.le]), intervalIntegral.integral_const]
  simp

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
theorem attachmentHazard_before_boundary {N : ℕ} (T : Tree N) (t x : ℝ)
    (ht : t < rootHeight T) (hx : t ≤ x) (hxb : x ≤ nextBoundary T t) :
    attachmentHazard T t x = attachmentRate T t * (x - t) := by
  unfold attachmentHazard
  rw [intervalIntegral.integral_congr_Ioo_of_le hx
    (g := fun _ => attachmentRate T t) (fun s hs =>
      attachmentRate_eq_before_boundary T t s ht hs.1.le (hs.2.trans_le hxb)),
    intervalIntegral.integral_const]
  exact mul_comm _ _

theorem future_boundaries_strict_decrease {N : ℕ} (T : Tree N) (t : ℝ)
    (ht : t < rootHeight T) :
    ((attachmentBoundaries T).filter (fun b => nextBoundary T t < b)).card <
      ((attachmentBoundaries T).filter (fun b => t < b)).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro b hb
    simp only [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, (next_boundary_strict T t ht).trans hb.2⟩
  · intro he
    have hm : nextBoundary T t ∈ (attachmentBoundaries T).filter (fun b => t < b) :=
      Finset.mem_filter.mpr ⟨next_boundary_mem T t, next_boundary_strict T t ht⟩
    rw [← he] at hm
    simp at hm
end Rhone.Coalescent.SmcPrime
