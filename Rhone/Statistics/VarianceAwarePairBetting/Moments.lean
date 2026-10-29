/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.LogBounds
public import Rhone.Statistics.DependentPairedTest.FiniteProbability

/-! # One-third calibration and log-moment bounds -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

def tuning (δ r : ℝ) : ℝ := δ / (3 * r)
def signal (δ r : ℝ) : ℝ := δ ^ 2 / r

theorem tuning_bounds {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) :
    0 < tuning δ r ∧ tuning δ r ≤ 1 / 3 := by
  have hr := hδ.trans_le hδr
  constructor
  · exact div_pos hδ (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < 3 * r)).mpr
    linarith

theorem tuning_product_bound {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    {z : ℝ} (hz : |z| ≤ 1) : |tuning δ r * z| ≤ 1 / 3 := by
  rw [abs_mul, abs_of_pos (tuning_bounds hδ hδr).1]
  exact (mul_le_of_le_one_right (tuning_bounds hδ hδr).1.le hz).trans
    (tuning_bounds hδ hδr).2

theorem source_log_mean (P : Law X) (Z : X → ℝ) {δ r : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hZ : ∀ x, |Z x| ≤ 1)
    (hm : rejection P Z = δ) (hs : rejection P (fun x => Z x ^ 2) = r) :
    2 * signal δ r / 9 ≤ rejection P (fun x => Real.log (1 + tuning δ r * Z x)) := by
  have hr := hδ.trans_le hδr
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (log_one_add_lower (tuning_product_bound hδ hδr (hZ x)))
      (P.nonneg x))
  have he : (∑ x, P.mass x * (tuning δ r * Z x - (tuning δ r * Z x) ^ 2)) =
      tuning δ r * δ - tuning δ r ^ 2 * r := by
    simp only [mul_sub, mul_pow, Finset.sum_sub_distrib]
    have h1 : (∑ x, P.mass x * (tuning δ r * Z x)) = tuning δ r * rejection P Z := by
      simp only [rejection, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    have h2 : (∑ x, P.mass x * (tuning δ r ^ 2 * Z x ^ 2)) =
        tuning δ r ^ 2 * rejection P (fun x => Z x ^ 2) := by
      simp only [rejection, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    rw [h1, h2, hm, hs]
  rw [he] at h
  have ha : tuning δ r * δ - tuning δ r ^ 2 * r = 2 * signal δ r / 9 := by
    unfold tuning signal
    field_simp [ne_of_gt hr]
    ring
  rw [ha] at h
  exact h

theorem source_log_second (P : Law X) (Z : X → ℝ) {δ r : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hZ : ∀ x, |Z x| ≤ 1)
    (hs : rejection P (fun x => Z x ^ 2) = r) :
    rejection P (fun x => Real.log (1 + tuning δ r * Z x) ^ 2) ≤ signal δ r / 4 := by
  have hr := hδ.trans_le hδr
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (log_one_add_sq_upper (tuning_product_bound hδ hδr (hZ x)))
      (P.nonneg x))
  have he : (∑ x, P.mass x * (9 / 4 * (tuning δ r * Z x) ^ 2)) =
      9 / 4 * tuning δ r ^ 2 * rejection P (fun x => Z x ^ 2) := by
    simp only [rejection, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  rw [he, hs] at h
  have ha : 9 / 4 * tuning δ r ^ 2 * r = signal δ r / 4 := by
    unfold tuning signal
    field_simp [ne_of_gt hr]
    ring
  rw [ha] at h
  exact h

end Rhone.Statistics.VarianceAwarePairBetting
