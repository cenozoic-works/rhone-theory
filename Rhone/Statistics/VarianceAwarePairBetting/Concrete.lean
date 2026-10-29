/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.SymmetricIslandChannel
public import Rhone.Statistics.SelfNormalizedPairTest.Concrete
public import Rhone.Statistics.GeneralPairTimePower.PooledWitness

/-! # The 400000-pair low-mutation endpoint with the calibrated bet held fixed -/

@[expose] public section

namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget DependentPairedTest LinkedAgreementPower
open PairObservationChannel SelfNormalizedPairTest GeneralPairTimePower

noncomputable def lowTuning : ℝ := pairedTuning lowWithin lowBetween agreementIndicator

theorem low_tuning_bound : |lowTuning| ≤ 1 / 3 := by
  apply paired_tuning_bound _ _ agreementIndicator agreement_binary
  rw [low_within_mean, low_between_mean]
  norm_num

theorem concrete_low_mutation_power :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair lowWithin lowBetween) 400000)
      (Rejects lowTuning (pairedContrast agreementIndicator)) := by
  apply pair_source_power _ _ agreementIndicator agreement_binary 400000
  · rw [low_within_mean, low_between_mean]
    norm_num
  · rw [low_within_mean, low_between_mean]
    norm_num

theorem concrete_common_law_size (P : Law (Fin 4 × Fin 4)) :
    probability (iid (independentPair P P) 400000)
      (Rejects lowTuning (pairedContrast agreementIndicator)) ≤ (1 : ℝ) / 20 :=
  common_pair_size P agreementIndicator agreement_binary 400000 low_tuning_bound

theorem concrete_pan_size (r : ℝ → ℝ) (hr : AdmittedPan r) {k : ℝ} (hk : 0 ≤ k) :
    probability (iid (independentPair
      (panObservedLaw (identityChannel 4 (by norm_num)) r hr hk)
      (panObservedLaw (identityChannel 4 (by norm_num)) r hr hk)) 400000)
      (Rejects lowTuning (pairedContrast agreementIndicator)) ≤ (1 : ℝ) / 20 :=
  concrete_common_law_size _

end Rhone.Statistics.VarianceAwarePairBetting
