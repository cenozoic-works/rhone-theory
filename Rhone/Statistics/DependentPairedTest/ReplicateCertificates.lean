/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Calibrated
public import Rhone.Statistics.DependentPairedTest.Source
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting

/-! # 500-replicate certificates, preserving within-pair scope -/

@[expose] public section

namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget LinkedAgreementPower

theorem clean_contrast_bounded (x : CleanPair × CleanPair) :
    |cleanAgreement x.1 - cleanAgreement x.2| ≤ 1 := by
  rcases clean_agreement_binary x.1 with h | h <;>
    rcases clean_agreement_binary x.2 with g | g <;> simp [h, g]

theorem coupling_calibrated_power_500 (R : Law (CleanPair × CleanPair))
    (hR : IsCoupling R cleanWithin cleanBetween) :
    (19 : ℝ) / 20 ≤ probability (iid R 500)
      (calibratedRejects (fun x => cleanAgreement x.1 - cleanAgreement x.2)) := by
  apply calibrated_source_power R _ clean_contrast_bounded
  change contrastMean R (fun x => cleanAgreement x.1) (fun x => cleanAgreement x.2) = _
  rw [coupling_contrast_mean R cleanWithin cleanBetween hR, clean_marginal_gap]

theorem common_coupling_calibrated_size_500 (P : Law CleanPair)
    (R : Law (CleanPair × CleanPair)) (hR : IsCoupling R P P) :
    probability (iid R 500)
      (calibratedRejects (fun x => cleanAgreement x.1 - cleanAgreement x.2)) ≤ (1 : ℝ) / 20 := by
  apply calibrated_null_size R _ clean_contrast_bounded
  change contrastMean R (fun x => cleanAgreement x.1) (fun x => cleanAgreement x.2) = _
  rw [coupling_contrast_mean R P P hR, sub_self]

theorem independent_calibrated_power_500 :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair cleanWithin cleanBetween) 500)
      (calibratedRejects (fun x => cleanAgreement x.1 - cleanAgreement x.2)) :=
  coupling_calibrated_power_500 _ (independent_coupling cleanWithin cleanBetween)

theorem common_independent_calibrated_size_500 (P : Law CleanPair) :
    probability (iid (independentPair P P) 500)
      (calibratedRejects (fun x => cleanAgreement x.1 - cleanAgreement x.2)) ≤ (1 : ℝ) / 20 :=
  common_coupling_calibrated_size_500 P _ (independent_coupling P P)

end Rhone.Statistics.DependentPairedTest
