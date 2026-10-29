/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSample
public import Rhone.Coalescent.SmcPrimeTwoSampleAgreement
public import Rhone.Coalescent.SmcPrimeTVBound

/-!
# Two samples: lower bound on total variation between the ARG and SMC′ genealogy laws

Source: wilton_carmi_hobolth2015, eq. (5), (7). -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MarkovChain.IntervalProcess SmcBound Analysis Rhone.Combinatorics MarkovChain
    Probability MeasureTheory
open scoped ENNReal

theorem fullARG_smcPrime_tv_two_sample_abs_lower (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    ENNReal.ofReal
        |SmcPrime.argAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ))) -
          SmcPrime.smcPrimeAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ)))| ≤
      eventTV (fullARGGenealogyLaw 2 R) (smcPrimeGenealogyLaw 2 R) := by
  have hρ : 0 ≤ R * ((y.val : ℝ) - (x.val : ℝ)) :=
    mul_nonneg hR (sub_nonneg.2 (by exact_mod_cast hxy.le))
  have hA : (fullARGGenealogyLaw 2 R).real (twoSampleAgreement x y) =
      SmcPrime.argAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ))) := by
    rw [measureReal_def]
    exact (congrArg ENNReal.toReal (fullARG_two_sample_agreement_prob R hR x y hxy)).trans
      (ENNReal.toReal_ofReal (SmcPrime.argAgreementProb_pos hρ).le)
  have hS : (smcPrimeGenealogyLaw 2 R).real (twoSampleAgreement x y) =
      SmcPrime.smcPrimeAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ))) := by
    rw [measureReal_def, smcPrime_two_sample_agreement_prob R hR x y hxy,
      ENNReal.toReal_ofReal (SmcPrime.smcPrimeAgreementProb_pos hρ).le]
  rw [← hA, ← hS]
  exact (eventTV_le_iff _ _ _).1 le_rfl _ (twoSampleAgreement_measurable x y)

theorem fullARG_smcPrime_tv_two_sample_lower (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    ENNReal.ofReal
        (SmcPrime.argAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ))) -
          SmcPrime.smcPrimeAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ)))) ≤
      eventTV (fullARGGenealogyLaw 2 R) (smcPrimeGenealogyLaw 2 R) :=
  (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (fullARG_smcPrime_tv_two_sample_abs_lower R hR x y hxy)

theorem fullARG_smcPrime_tv_two_sample_quadratic_lower (c : ℝ) (hc : c < 13 / 270) :
    ∀ᶠ R in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ENNReal.ofReal (c * R ^ 2) ≤
        eventTV (fullARGGenealogyLaw 2 R) (smcPrimeGenealogyLaw 2 R) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · filter_upwards with R
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc0 (sq_nonneg R))]
    exact zero_le
  have ht : Real.sqrt (c * (270 / 13)) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  obtain ⟨q, hq, hq1⟩ := exists_rat_btwn ht
  have hq0 : (0 : ℝ) < q := (Real.sqrt_nonneg _).trans_lt hq
  have hqsq : c * (270 / 13) < (q : ℝ) ^ 2 := (Real.sqrt_lt' hq0).1 hq
  have hε : 0 < (q : ℝ) ^ 2 * (13 / 270) - c := by linarith
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hε)] with R hR
  have hR0 : 0 < R := hR.1
  have hR1 : R < 1 := hR.2.trans_le (min_le_left _ _)
  have hRε : R < (q : ℝ) ^ 2 * (13 / 270) - c := hR.2.trans_le (min_le_right _ _)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hq1' : q < 1 := by exact_mod_cast hq1
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (fullARG_smcPrime_tv_two_sample_lower R hR0.le
      (⟨0, le_rfl, zero_lt_one⟩ : GenomicProbe) (⟨q, hq0'.le, hq1'⟩ : GenomicProbe) hq0')
  have hρ : R * (((q : ℚ) : ℝ) - ((0 : ℚ) : ℝ)) = R * q := by
    rw [Rat.cast_zero, sub_zero]
  rw [hρ]
  have hρ0 : 0 ≤ R * q := mul_nonneg hR0.le hq0.le
  have hρR : R * q ≤ R := mul_le_of_le_one_right hR0.le hq1.le
  have hρ1 : R * q ≤ 1 := hρR.trans hR1.le
  have h1 := SmcPrime.le_argAgreementProb_sub_smcPrimeAgreementProb_sub hρ0
  have h3 : (R * q) ^ 3 ≤ (R * q) ^ 2 * R := by
    have := mul_le_mul_of_nonneg_left hρR (sq_nonneg (R * q))
    nlinarith
  have h4 : (R * q) ^ 4 ≤ (R * q) ^ 2 * R := by
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul hρR hρ1 hρ0 hR0.le) (sq_nonneg (R * q))
    nlinarith
  have h5 : 0 ≤ (R * q) ^ 2 * R := mul_nonneg (sq_nonneg _) hR0.le
  have hq2 : (q : ℝ) ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have h6 := mul_nonneg (sq_nonneg R)
    (add_nonneg (sub_nonneg.2 hRε.le) (mul_nonneg hR0.le (sub_nonneg.2 hq2)))
  nlinarith

end Rhone.Coalescent.SmcPrime
