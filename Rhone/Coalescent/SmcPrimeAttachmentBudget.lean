/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeLengthGeometry
public import Rhone.Coalescent.SmcSupport.HistoryNoise
public import Rhone.MarkovChain.JumpHold

/-!
# Attachment-time budget bound and mean waiting time of the attachment recursion

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory
open scoped ENNReal

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def TreeTemporalCover {N : ℕ} (T : Tree N) : Prop :=
  ∀ t, 0 ≤ t → t < rootHeight T → (activeBranches T t).Nonempty

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem attachment_rate_ge_one {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t : ℝ) (ht : 0 ≤ t) : 1 ≤ attachmentRate T t := by
  by_cases hr : rootHeight T ≤ t
  · simp [attachmentRate, hr]
  · have hc : 1 ≤ (activeBranches T t).card := Finset.one_le_card.mpr (hT t ht (lt_of_not_ge hr))
    simp only [attachmentRate, ite_eq_right hr]
    exact_mod_cast hc

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem next_boundary_bounds {N : ℕ} (T : Tree N) (t : ℝ)
    (ht : t ≤ rootHeight T) : t ≤ nextBoundary T t ∧ nextBoundary T t ≤ rootHeight T := by
  have hfold (l : List ℝ) (z : ℝ) (hz : t ≤ z ∧ z ≤ rootHeight T) :
      t ≤ l.foldr (fun h a => if t < h then min h a else a) z ∧
      l.foldr (fun h a => if t < h then min h a else a) z ≤ rootHeight T := by
    induction l with
    | nil => exact hz
    | cons b rest ih =>
      simp only [List.foldr]
      by_cases hb : t < b
      · simp only [ite_eq_left hb]
        exact ⟨le_min hb.le ih.1, (min_le_right _ _).trans ih.2⟩
      · simpa only [ite_eq_right hb] using ih
  exact hfold _ _ ⟨ht, le_rfl⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem attachment_aux_budget_bound {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (k : ℕ) (t e : ℝ) (ht : 0 ≤ t) (he : 0 ≤ e) :
    t ≤ attachmentAux T k t e ∧ attachmentAux T k t e ≤ t + e := by
  induction k generalizing t e with
  | zero => exact ⟨by simpa only [attachmentAux] using le_add_of_nonneg_right he, le_rfl⟩
  | succ k ih =>
    by_cases hr : rootHeight T ≤ t
    · simp only [attachmentAux, ite_eq_left hr]
      exact ⟨le_add_of_nonneg_right he, le_rfl⟩
    · have hn := next_boundary_bounds T t (le_of_lt (lt_of_not_ge hr))
      have hrate := attachment_rate_ge_one T hT t ht
      have hrate0 : 0 < attachmentRate T t := by linarith
      have hstep : nextBoundary T t - t ≤ attachmentRate T t * (nextBoundary T t - t) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hn.1)
      by_cases hb : e < attachmentRate T t * (nextBoundary T t - t)
      · simp only [attachmentAux, ite_eq_right hr, ite_eq_left hb]
        have hupper : e / attachmentRate T t ≤ e := by
          apply (div_le_iff₀ hrate0).mpr
          nlinarith [mul_le_mul_of_nonneg_left hrate he]
        exact ⟨le_add_of_nonneg_right (div_nonneg he hrate0.le), by linarith⟩
      · simp only [attachmentAux, ite_eq_right hr, ite_eq_right hb]
        have hbudget : 0 ≤ e - attachmentRate T t * (nextBoundary T t - t) := by
          linarith
        have hrec := ih (nextBoundary T t)
          (e - attachmentRate T t * (nextBoundary T t - t)) (ht.trans hn.1) hbudget
        exact ⟨hn.1.trans hrec.1, by linarith [hrec.2]⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem attachment_time_budget_bound {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t e : ℝ) (ht : 0 ≤ t) (he : 0 ≤ e) :
    t ≤ attachmentTime T t e ∧ attachmentTime T t e ≤ t + e :=
  attachment_aux_budget_bound T hT _ t e ht he

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem inverse_log_budget_mean :
    ∫⁻ u, ENNReal.ofReal (-Real.log u) ∂Rhone.Coalescent.IntervalProcess.unitUniform = 1 := by
  have hmap := Rhone.Coalescent.SmcSupport.inverseClock_law 1 (by norm_num)
  simp only [div_one] at hmap
  rw [← Rhone.MarkovChain.lintegral_ofReal_expMeasure_one, ← hmap,
    lintegral_map (by fun_prop) (by fun_prop)]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem attachment_wait_mean_le {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ u, ENNReal.ofReal (attachmentTime T t (-Real.log u) - t)
      ∂Rhone.Coalescent.IntervalProcess.unitUniform) ≤ 1 := by
  rw [← inverse_log_budget_mean]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have he : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
  apply ENNReal.ofReal_le_ofReal
  have hbound := (attachment_time_budget_bound T hT t (-Real.log u) ht he).2
  linarith

end Rhone.Coalescent.SmcPrime
