/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.PatternScore
public import Rhone.Statistics.ThreeSiteSeparator.SourceLaplace

/-! # The five genealogy features as concrete integer-clock Laplace combinations -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability ThreeTipSites SingleSiteChannel

def monomialKernel (p q : ℕ) (t : ℝ × ℝ) : ℝ :=
  Real.exp (-((p : ℝ)+q)*t.1-(q : ℝ)*t.2)

def combinedKernel (p q r s : ℕ) (t : ℝ × ℝ) : ℝ :=
  (monomialKernel p q t+2*monomialKernel r s t)/3

lemma monomialKernel_powers (p q : ℕ) (t : ℝ × ℝ) :
    monomialKernel p q t = Real.exp (-t.1)^p*Real.exp (-(t.1+t.2))^q := by
  unfold monomialKernel
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma decay_two (x : ℝ) : Real.exp (-2*x) = Real.exp (-x)^2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma internal_two (t : ℝ × ℝ) :
    secondMomentKernel 2 t = Real.exp (-t.1)*Real.exp (-(t.1+t.2))^2 := by
  unfold secondMomentKernel
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma genealogy_integrands_two (t : ℝ × ℝ) :
    (Real.exp (-2*t.1)+2*Real.exp (-2*(t.1+t.2)))/3 = combinedKernel 2 0 0 2 t ∧
    (Real.exp (-2*t.1)^2+2*Real.exp (-2*(t.1+t.2))^2)/3 = combinedKernel 4 0 0 4 t ∧
    (Real.exp (-2*t.1)^3+2*Real.exp (-2*(t.1+t.2))^3)/3 = combinedKernel 6 0 0 6 t ∧
    secondMomentKernel 2 t*(Real.exp (-2*t.1)^2+2*Real.exp (-2*(t.1+t.2))^2)/3 =
      combinedKernel 5 2 1 6 t ∧
    secondMomentKernel 2 t*(2*Real.exp (-2*t.1)*Real.exp (-2*(t.1+t.2))+
      Real.exp (-2*(t.1+t.2))^2)/3 = combinedKernel 1 6 3 4 t := by
  simp only [combinedKernel, monomialKernel_powers, decay_two, internal_two,
    pow_zero, one_mul, mul_one]
  repeat' constructor
  all_goals ring

lemma monomialKernel_integrable (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (p q : ℕ) : Integrable (monomialKernel p q) μ := by
  apply Integrable.of_bound (by unfold monomialKernel; fun_prop) 1
  filter_upwards [hμ] with t ht
  unfold monomialKernel
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have h1 : 0 ≤ ((p : ℝ)+q)*t.1 := mul_nonneg (by positivity) ht.1
  have h2 : 0 ≤ (q : ℝ)*t.2 := mul_nonneg (by positivity) ht.2
  linarith

lemma combinedKernel_integral (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (p q r s : ℕ) :
    (∫ t, combinedKernel p q r s t ∂μ) =
      ((∫ t, monomialKernel p q t ∂μ)+2*(∫ t, monomialKernel r s t ∂μ))/3 := by
  unfold combinedKernel
  rw [integral_div, integral_add (monomialKernel_integrable μ hμ p q)
    ((monomialKernel_integrable μ hμ r s).const_mul 2), integral_const_mul]

lemma genealogyScore_two_laplace (μ : Measure (ℝ × ℝ)) :
    genealogyScore 2 μ =
      score (∫ t, combinedKernel 2 0 0 2 t ∂μ) (∫ t, combinedKernel 4 0 0 4 t ∂μ)
        (∫ t, combinedKernel 6 0 0 6 t ∂μ) (∫ t, combinedKernel 5 2 1 6 t ∂μ)
        (∫ t, combinedKernel 1 6 3 4 t ∂μ) := by
  unfold genealogyScore
  simp_rw [(genealogy_integrands_two _).1, (genealogy_integrands_two _).2.1,
    (genealogy_integrands_two _).2.2.1, (genealogy_integrands_two _).2.2.2.1,
    (genealogy_integrands_two _).2.2.2.2]

end Rhone.Statistics.ThreeSiteSeparator
