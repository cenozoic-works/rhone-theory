/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SingleSite.UnitMoments

/-! # Six candidate stationary two-site features -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.TwoSiteStationary
open SingleSiteChannel SingleSite

def firstPair (k : ℝ) (p : ℝ × ℝ) : ℝ := Real.exp (-k * p.1)
def rootPair (k : ℝ) (p : ℝ × ℝ) : ℝ := Real.exp (-k * (p.1 + p.2))
def contrast (k : ℝ) (p : ℝ × ℝ) : ℝ := firstPair k p - rootPair k p

def samePairSquare (k : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((firstPair k p) ^ 2 + 2 * (rootPair k p) ^ 2) / 3

def differentPairProduct (k : ℝ) (p : ℝ × ℝ) : ℝ :=
  (2 * firstPair k p * rootPair k p + (rootPair k p) ^ 2) / 3

def features (k : ℝ) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  ![firstMomentKernel k p, secondMomentKernel k p, samePairSquare k p,
    differentPairProduct k p, firstMomentKernel k p * secondMomentKernel k p,
    (secondMomentKernel k p) ^ 2]

lemma first_mean_square (k : ℝ) (p : ℝ × ℝ) :
    (firstMomentKernel k p) ^ 2 = (samePairSquare k p + 2 * differentPairProduct k p) / 3 := by
  unfold firstMomentKernel samePairSquare differentPairProduct firstPair rootPair
  ring

lemma contrast_square (k : ℝ) (p : ℝ × ℝ) :
    (contrast k p) ^ 2 = 3 * (samePairSquare k p - differentPairProduct k p) := by
  unfold contrast samePairSquare differentPairProduct
  ring

lemma pair_bounds {k : ℝ} (hk : 0 ≤ k) (p : ℝ × ℝ) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (0 ≤ firstPair k p ∧ firstPair k p ≤ 1) ∧ (0 ≤ rootPair k p ∧ rootPair k p ≤ 1) := by
  refine ⟨⟨(Real.exp_pos _).le, ?_⟩, ⟨(Real.exp_pos _).le, ?_⟩⟩
  · exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) hp.1)
  · exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) (add_nonneg hp.1 hp.2))

lemma features_bounds {k : ℝ} (hk : 0 ≤ k) (p : ℝ × ℝ) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2)
    (i : Fin 6) : 0 ≤ features k p i ∧ features k p i ≤ 1 := by
  have hx := (pair_bounds hk p hp).1
  have hy := (pair_bounds hk p hp).2
  have ha := first_kernel_bounds hk p hp
  have hb := second_kernel_bounds hk p hp
  have hxx : (firstPair k p) ^ 2 ≤ 1 := by
    simpa only [pow_two] using (mul_le_of_le_one_left hx.1 hx.2).trans hx.2
  have hyy : (rootPair k p) ^ 2 ≤ 1 := by
    simpa only [pow_two] using (mul_le_of_le_one_left hy.1 hy.2).trans hy.2
  have hxy : firstPair k p * rootPair k p ≤ 1 := (mul_le_of_le_one_left hy.1 hx.2).trans hy.2
  fin_cases i
  · exact ha
  · exact hb
  · change 0 ≤ samePairSquare k p ∧ samePairSquare k p ≤ 1
    unfold samePairSquare
    constructor
    · positivity
    · linarith
  · change 0 ≤ differentPairProduct k p ∧ differentPairProduct k p ≤ 1
    unfold differentPairProduct
    constructor
    · exact div_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx.1) hy.1)
        (sq_nonneg _)) (by norm_num)
    · linarith
  · exact ⟨mul_nonneg ha.1 hb.1, (mul_le_of_le_one_left hb.1 ha.2).trans hb.2⟩
  · change 0 ≤ (secondMomentKernel k p) ^ 2 ∧ (secondMomentKernel k p) ^ 2 ≤ 1
    exact ⟨sq_nonneg _, by simpa only [pow_two] using (mul_le_of_le_one_left hb.1 hb.2).trans hb.2⟩

lemma features_measurable (k : ℝ) (i : Fin 6) : Measurable (fun p => features k p i) := by
  fin_cases i <;> unfold features firstMomentKernel secondMomentKernel samePairSquare
    differentPairProduct firstPair rootPair <;> fun_prop

lemma features_integrable (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : ThreeTipSites.NonnegativeTimes μ) {k : ℝ} (hk : 0 ≤ k) (i : Fin 6) :
    Integrable (fun p => features k p i) μ := by
  refine Integrable.of_bound (features_measurable k i).aestronglyMeasurable 1 ?_
  filter_upwards [hμ] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (features_bounds hk p hp i).1]
  exact (features_bounds hk p hp i).2

end Rhone.Statistics.TwoSiteStationary
