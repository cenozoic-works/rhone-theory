/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SelfNormalizedPairTest.IndependentStrata

/-! # Low-mutation endpoint from source-law rational means -/

@[expose] public section

namespace Rhone.Statistics.SelfNormalizedPairTest
open DependenceBudget DependentPairedTest LinkedAgreementPower
open PairObservationChannel SpatialPairDesign MarkovChain.Identifiability Identifiability

noncomputable def lowWithin : Law (Fin 4 × Fin 4) :=
  sourceLaw (identityChannel 4 (by norm_num)) 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (0 : ℝ) ≤ 1 / 100000) 0

noncomputable def lowBetween : Law (Fin 4 × Fin 4) :=
  sourceLaw (identityChannel 4 (by norm_num)) 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (0 : ℝ) ≤ 1 / 100000) 1

theorem low_within_mean :
    rejection lowWithin agreementIndicator = (800404001 : ℝ) / 800416004 := by
  rw [lowWithin, source_agreement_mean, identity_baseline, identity_variance]
  norm_num [pairLaplacePotential, pairLaplaceDenominator]

theorem low_between_mean :
    rejection lowBetween agreementIndicator = (800104001 : ℝ) / 800416004 := by
  rw [lowBetween, source_agreement_mean, identity_baseline, identity_variance]
  norm_num [pairLaplacePotential, pairLaplaceDenominator]

theorem low_independent_discordance :
    discordance (independentPair lowWithin lowBetween)
      (fun x => agreementIndicator x.1) (fun x => agreementIndicator x.2) =
        (129666048924003 : ℝ) / 320332889729664008 := by
  rw [independent_discordance _ _ agreement_binary, low_within_mean, low_between_mean]
  norm_num

theorem concrete_low_mutation_power :
    (19 : ℝ) / 20 ≤ independentTest lowWithin lowBetween agreementIndicator 500000 := by
  apply binary_signed_power _ _ agreement_binary 500000
  · rw [low_within_mean, low_between_mean]
    norm_num
  · rw [low_within_mean, low_between_mean]
    norm_num

theorem concrete_common_law_size (P : Law (Fin 4 × Fin 4)) :
    independentTest P P agreementIndicator 500000 ≤ (1 : ℝ) / 20 := common_pair_size P 500000

end Rhone.Statistics.SelfNormalizedPairTest
