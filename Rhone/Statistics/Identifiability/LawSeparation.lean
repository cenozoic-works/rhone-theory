/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.JointRestriction

/-! # Joint-law separation from deterministic conditional coalescence clocks -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

def timeBox : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioi (1 : ℝ)

theorem timeBox_measurable : MeasurableSet timeBox :=
  measurableSet_Ioo.prod measurableSet_Ioi

theorem timeBox_subset_wedge : timeBox ⊆ upperWedge := by
  intro p hp
  exact ⟨hp.1.1, lt_trans hp.1.2 hp.2⟩

theorem jointLaw_restrict_box (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    (jointLaw k c q r).restrict timeBox = upperBoxLaw k c q r := by
  rw [← Measure.restrict_restrict_of_subset timeBox_subset_wedge,
    jointLaw_restrict_upper k hc hq hr, upperEventLaw_density k hc hq hr,
    restrict_withDensity timeBox_measurable,
    Measure.restrict_restrict_of_subset timeBox_subset_wedge]
  unfold upperBoxLaw timeBoxMeasure
  rw [Measure.prod_restrict]
  rfl

theorem island_jointLaw_ne_factorized_law (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) (μ : Measure (ℝ × ℝ)) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t)
    (hμ : μ.restrict timeBox =
      timeBoxMeasure.withDensity (fun p => ENNReal.ofReal (a p.1 * b p.2))) :
    jointLaw k c q r ≠ μ := by
  intro heq
  apply upperBoxLaw_ne_product_density k hc hq hr a b ha hb ha0 hb0
  rw [← jointLaw_restrict_box k hc.le hq.le hr.le, heq, hμ]

noncomputable def panClockDensity (B rate H : ℝ → ℝ) (s t : ℝ) : ℝ :=
  B s * rate t * Real.exp (H s - H t)

theorem panClockDensity_factorization (B rate H : ℝ → ℝ) (s t : ℝ) :
    panClockDensity B rate H s t =
      (B s * Real.exp (H s)) * (rate t * Real.exp (-H t)) := by
  rw [panClockDensity, sub_eq_add_neg, Real.exp_add]
  ring

theorem island_jointLaw_ne_pan_clock (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) (μ : Measure (ℝ × ℝ))
    (B rate H : ℝ → ℝ) (hB : Measurable B) (hrate : Measurable rate) (hH : Measurable H)
    (hB0 : ∀ t, 0 ≤ B t) (hrate0 : ∀ t, 0 ≤ rate t)
    (hμ : μ.restrict timeBox = timeBoxMeasure.withDensity
      (fun p => ENNReal.ofReal (panClockDensity B rate H p.1 p.2))) :
    jointLaw k c q r ≠ μ := by
  apply island_jointLaw_ne_factorized_law k hc hq hr μ
    (fun s => B s * Real.exp (H s)) (fun t => rate t * Real.exp (-H t))
    (hB.mul hH.exp) (hrate.mul hH.neg.exp)
    (fun s => mul_nonneg (hB0 s) (Real.exp_pos _).le)
    (fun t => mul_nonneg (hrate0 t) (Real.exp_pos _).le)
  simpa only [panClockDensity_factorization] using hμ

end Rhone.Statistics.Identifiability
