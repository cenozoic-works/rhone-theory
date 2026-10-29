/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeAttachmentHazard
/-!
# The finite-depth attachment recursion inverts the cumulative attachment hazard

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–6. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess

theorem attachment_aux_budget_iff {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (k : ℕ) (t e x : ℝ)
    (ht : 0 ≤ t) (he : 0 ≤ e) (hx : t ≤ x)
    (hk : ((attachmentBoundaries T).filter (fun b => t < b)).card ≤ k) :
    attachmentAux T k t e ≤ x ↔ e ≤ attachmentHazard T t x := by
  classical
  induction k generalizing t e x with
  | zero =>
    have hr : rootHeight T ≤ t := by
      by_contra hn
      have hm : rootHeight T ∈ (attachmentBoundaries T).filter (fun b => t < b) := by
        simp [attachmentBoundaries, lt_of_not_ge hn]
      have hc := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    rw [attachmentAux, attachmentHazard_above_root T t x hr hx]
    constructor <;> intro h <;> linarith
  | succ k ih =>
    by_cases hr : rootHeight T ≤ t
    · rw [attachmentAux, ite_eq_left hr, attachmentHazard_above_root T t x hr hx]
      constructor <;> intro h <;> linarith
    · have htr : t < rootHeight T := lt_of_not_ge hr
      have hnb := next_boundary_bounds T t htr.le
      have hns := next_boundary_strict T t htr
      have hrate := attachment_rate_ge_one T hT t ht
      have hrate0 : 0 < attachmentRate T t := by linarith
      have hk' : ((attachmentBoundaries T).filter
          (fun b => nextBoundary T t < b)).card ≤ k := by
        have hd := future_boundaries_strict_decrease T t htr
        omega
      by_cases heb : e < attachmentRate T t * (nextBoundary T t - t)
      · simp only [attachmentAux, ite_eq_right hr, ite_eq_left heb]
        by_cases hxb : x < nextBoundary T t
        · rw [attachmentHazard_before_boundary T t x htr hx hxb.le]
          constructor
          · intro h
            have hd : e / attachmentRate T t ≤ x - t := by linarith
            have hm := (div_le_iff₀ hrate0).mp hd
            nlinarith
          · intro h
            have hd : e / attachmentRate T t ≤ x - t :=
              (div_le_iff₀ hrate0).mpr (by nlinarith)
            linarith
        · have hnx : nextBoundary T t ≤ x := le_of_not_gt hxb
          have hw : t + e / attachmentRate T t < nextBoundary T t := by
            have hd : e / attachmentRate T t < nextBoundary T t - t :=
              (div_lt_iff₀ hrate0).mpr (by nlinarith)
            linarith
          have hadd := attachmentHazard_add T t (nextBoundary T t) x
          rw [attachmentHazard_before_boundary T t (nextBoundary T t) htr hnb.1 le_rfl]
            at hadd
          have hn0 := attachmentHazard_nonneg T (nextBoundary T t) x hnx
          constructor
          · intro _; linarith
          · intro _; exact hw.le.trans hnx
      · have he' : 0 ≤ e - attachmentRate T t * (nextBoundary T t - t) := by
          linarith
        simp only [attachmentAux, ite_eq_right hr, ite_eq_right heb]
        by_cases hxb : x < nextBoundary T t
        · have hbound := attachment_aux_budget_bound T hT k (nextBoundary T t)
            (e - attachmentRate T t * (nextBoundary T t - t)) (ht.trans hnb.1) he'
          rw [attachmentHazard_before_boundary T t x htr hx hxb.le]
          constructor
          · intro h; exfalso; linarith [hbound.1]
          · intro h; exfalso; nlinarith
        · have hnx : nextBoundary T t ≤ x := le_of_not_gt hxb
          rw [ih (nextBoundary T t)
            (e - attachmentRate T t * (nextBoundary T t - t)) x
            (ht.trans hnb.1) he' hnx hk']
          have hadd := attachmentHazard_add T t (nextBoundary T t) x
          rw [attachmentHazard_before_boundary T t (nextBoundary T t) htr hnb.1 le_rfl]
            at hadd
          constructor <;> intro h <;> linarith

theorem attachment_time_budget_iff {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t e x : ℝ)
    (ht : 0 ≤ t) (he : 0 ≤ e) (hx : t ≤ x) :
    attachmentTime T t e ≤ x ↔ e ≤ attachmentHazard T t x := by
  apply attachment_aux_budget_iff T hT _ t e x ht he hx
  exact (Finset.card_filter_le _ _).trans (attachment_boundaries_card T)
end Rhone.Coalescent.SmcPrime
