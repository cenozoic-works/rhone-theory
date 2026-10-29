/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.Paired
public import Rhone.Statistics.SelfNormalizedPairTest.IndependentStrata

/-! # Symmetric-island common-channel betting power -/

@[expose] public section

namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget DependentPairedTest LinkedAgreementPower
open PairObservationChannel SpatialPairDesign SelfNormalizedPairTest
open MarkovChain.Identifiability Identifiability
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem reported_agreement_positive (E : Channel K H) (hE : Informative E) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) :
    rejection (sourceLaw E n hc hq hk.le 1) agreementIndicator <
      rejection (sourceLaw E n hc hq hk.le 0) agreementIndicator := by
  have hg := source_agreement_gap E n hc hq hk.le
  change rejection _ agreementIndicator - rejection _ agreementIndicator = _ at hg
  have hp := mul_pos ((retained_variance_pos_iff E).mpr hE)
    (div_pos (mul_pos hc hk) (pairLaplaceDenominator_pos n hc hq hk.le))
  linarith

theorem reported_rate_power (E : Channel K H) (hE : Informative E) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) (N : ℕ)
    (hbudget : 128 * (rejection (sourceLaw E n hc hq hk.le 0) agreementIndicator +
      rejection (sourceLaw E n hc hq hk.le 1) agreementIndicator -
      2 * rejection (sourceLaw E n hc hq hk.le 0) agreementIndicator *
        rejection (sourceLaw E n hc hq hk.le 1) agreementIndicator) ≤
      N * (retainedVariance E * (c * k / pairLaplaceDenominator n c q k)) ^ 2) :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair (sourceLaw E n hc hq hk.le 0)
      (sourceLaw E n hc hq hk.le 1)) N)
      (Rejects (pairedTuning (sourceLaw E n hc hq hk.le 0)
        (sourceLaw E n hc hq hk.le 1) agreementIndicator) (pairedContrast agreementIndicator)) := by
  apply pair_source_power _ _ agreementIndicator agreement_binary N
    (reported_agreement_positive E hE n hc hq hk)
  have hg := source_agreement_gap E n hc hq hk.le
  change rejection _ agreementIndicator - rejection _ agreementIndicator = _ at hg
  rw [hg]
  exact hbudget

theorem reported_rate_common_size (E : Channel K H) (hE : Informative E) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) (N : ℕ) (P : Law (H × H)) :
    probability (iid (independentPair P P) N)
      (Rejects (pairedTuning (sourceLaw E n hc hq hk.le 0)
        (sourceLaw E n hc hq hk.le 1) agreementIndicator) (pairedContrast agreementIndicator)) ≤
      (1 : ℝ) / 20 :=
  common_pair_size P agreementIndicator agreement_binary N
    (paired_tuning_bound _ _ agreementIndicator agreement_binary
      (reported_agreement_positive E hE n hc hq hk))

end Rhone.Statistics.VarianceAwarePairBetting
