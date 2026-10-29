/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.PanSortedMoments
public import Rhone.Statistics.ThreeSiteSeparator.PatternScore

/-! # The five observed genealogy features at an arbitrary mutation clock -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

def scaledCombinedKernel (a : ℝ) (p q r s : ℕ) (t : ℝ × ℝ) : ℝ :=
  (scaledDurationKernel a p q t+2*scaledDurationKernel a r s t)/3

lemma decay_scaled (k x : ℝ) : Real.exp (-k*x) = Real.exp (-(k/2)*x)^2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma internal_scaled (k : ℝ) (t : ℝ × ℝ) :
    secondMomentKernel k t = Real.exp (-(k/2)*t.1)*Real.exp (-(k/2)*(t.1+t.2))^2 := by
  unfold secondMomentKernel
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma genealogy_integrands_scaled (k : ℝ) (t : ℝ × ℝ) :
    (Real.exp (-k*t.1)+2*Real.exp (-k*(t.1+t.2)))/3 =
      scaledCombinedKernel (k/2) 2 0 0 2 t ∧
    (Real.exp (-k*t.1)^2+2*Real.exp (-k*(t.1+t.2))^2)/3 =
      scaledCombinedKernel (k/2) 4 0 0 4 t ∧
    (Real.exp (-k*t.1)^3+2*Real.exp (-k*(t.1+t.2))^3)/3 =
      scaledCombinedKernel (k/2) 6 0 0 6 t ∧
    secondMomentKernel k t*(Real.exp (-k*t.1)^2+2*Real.exp (-k*(t.1+t.2))^2)/3 =
      scaledCombinedKernel (k/2) 5 2 1 6 t ∧
    secondMomentKernel k t*(2*Real.exp (-k*t.1)*Real.exp (-k*(t.1+t.2))+
      Real.exp (-k*(t.1+t.2))^2)/3 = scaledCombinedKernel (k/2) 1 6 3 4 t := by
  simp only [scaledCombinedKernel, scaledDurationKernel, decay_scaled k t.1,
    decay_scaled k (t.1+t.2), internal_scaled,
    pow_zero, one_mul, mul_one]
  repeat' constructor
  all_goals ring

lemma scaledDurationKernel_integrable {a : ℝ} (ha : 0 ≤ a)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (p q : ℕ) : Integrable (scaledDurationKernel a p q) μ := by
  apply Integrable.of_bound (by unfold scaledDurationKernel; fun_prop) 1
  filter_upwards [hμ] with t ht
  unfold scaledDurationKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul (pow_le_one₀ (Real.exp_pos _).le ?_) (pow_le_one₀ (Real.exp_pos _).le ?_)
    (by positivity) (by norm_num)).trans_eq (one_mul 1)
  · exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) ht.1)
  · exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (add_nonneg ht.1 ht.2))

lemma scaledCombinedKernel_integral {a : ℝ} (ha : 0 ≤ a)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (p q r s : ℕ) :
    (∫ t, scaledCombinedKernel a p q r s t ∂μ) =
      ((∫ t, scaledDurationKernel a p q t ∂μ)+2*(∫ t, scaledDurationKernel a r s t ∂μ))/3 := by
  unfold scaledCombinedKernel
  rw [integral_div, integral_add (scaledDurationKernel_integrable ha μ hμ p q)
    ((scaledDurationKernel_integrable ha μ hμ r s).const_mul 2), integral_const_mul]

lemma genealogyScore_scaled (k : ℝ) (μ : Measure (ℝ × ℝ)) :
    genealogyScore k μ =
      score (∫ t, scaledCombinedKernel (k/2) 2 0 0 2 t ∂μ)
        (∫ t, scaledCombinedKernel (k/2) 4 0 0 4 t ∂μ)
        (∫ t, scaledCombinedKernel (k/2) 6 0 0 6 t ∂μ)
        (∫ t, scaledCombinedKernel (k/2) 5 2 1 6 t ∂μ)
        (∫ t, scaledCombinedKernel (k/2) 1 6 3 4 t ∂μ) := by
  unfold genealogyScore
  simp_rw [(genealogy_integrands_scaled _ _).1, (genealogy_integrands_scaled _ _).2.1,
    (genealogy_integrands_scaled _ _).2.2.1, (genealogy_integrands_scaled _ _).2.2.2.1,
    (genealogy_integrands_scaled _ _).2.2.2.2]

end Rhone.Statistics.ThreeSiteSeparator
