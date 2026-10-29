/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting
public import Rhone.Statistics.SpatialPairDesign.Separation

/-! # Independent-stratum self-normalized pair test -/

@[expose] public section

namespace Rhone.Statistics.SelfNormalizedPairTest
open DependenceBudget DependentPairedTest LinkedAgreementPower
open PairObservationChannel SpatialPairDesign MarkovChain.Identifiability Identifiability
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

def agreementIndicator (x : H × H) : ℝ := if x.1 = x.2 then 1 else 0

omit [Fintype H] in
theorem agreement_binary : Binary (agreementIndicator (H := H)) := by
  intro x
  unfold agreementIndicator
  split_ifs <;> simp

theorem common_pair_size (P : Law (H × H)) (N : ℕ) :
    independentTest P P agreementIndicator N ≤ (1 : ℝ) / 20 :=
  binary_test_common_size P agreement_binary N

theorem source_agreement_mean (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) (i : Fin 2) :
    rejection (sourceLaw E n hc hq hk i) agreementIndicator =
      baseline E + retainedVariance E * pairLaplacePotential n c q k i := by
  rw [sourceLaw]
  unfold agreementIndicator
  rw [agreement_as_expectation, agreement_formula, pairLaplace_pairLaw_eq_potential n hc hq hk]

theorem reported_rate_power (E : Channel K H) (hE : Informative E) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) (N : ℕ)
    (hbudget :
      160 * (rejection (sourceLaw E n hc hq hk.le 0) agreementIndicator +
        rejection (sourceLaw E n hc hq hk.le 1) agreementIndicator -
        2 * rejection (sourceLaw E n hc hq hk.le 0) agreementIndicator *
          rejection (sourceLaw E n hc hq hk.le 1) agreementIndicator) ≤
      N * (retainedVariance E * (c * k / pairLaplaceDenominator n c q k)) ^ 2) :
    (19 : ℝ) / 20 ≤ independentTest (sourceLaw E n hc hq hk.le 0)
      (sourceLaw E n hc hq hk.le 1) agreementIndicator N := by
  apply binary_signed_power _ _ agreement_binary N
  · intro he
    have hg := source_agreement_gap E n hc hq hk.le
    change rejection _ agreementIndicator - rejection _ agreementIndicator = _ at hg
    rw [he, sub_self] at hg
    have hp := mul_pos ((retained_variance_pos_iff E).mpr hE)
      (div_pos (mul_pos hc hk) (pairLaplaceDenominator_pos n hc hq hk.le))
    linarith
  · have hg := source_agreement_gap E n hc hq hk.le
    change rejection _ agreementIndicator - rejection _ agreementIndicator = _ at hg
    rw [hg]
    exact hbudget

end Rhone.Statistics.SelfNormalizedPairTest
