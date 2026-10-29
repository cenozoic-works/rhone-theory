/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Concrete
public import Rhone.Statistics.SpatialPairDesign.Observation

/-! # Source-model certificate: 2700 replicates detect any within-pair coupling -/

@[expose] public section

namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget PairObservationChannel SpatialPairDesign

abbrev CleanPair := Fin 4 × Fin 4

noncomputable def cleanWithin : Law CleanPair :=
  sourceLaw (identityChannel 4 (by norm_num)) 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (0 : ℝ) ≤ 2) 0

noncomputable def cleanBetween : Law CleanPair :=
  sourceLaw (identityChannel 4 (by norm_num)) 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (0 : ℝ) ≤ 2) 1

def cleanAgreement (x : CleanPair) : ℝ := if x.1 = x.2 then 1 else 0

theorem clean_agreement_binary : Binary cleanAgreement := by
  intro x
  unfold cleanAgreement
  split_ifs <;> simp

theorem clean_marginal_gap :
    rejection cleanWithin cleanAgreement - rejection cleanBetween cleanAgreement = (15 : ℝ) / 61 :=
  clean_agreement_gap

theorem source_coupling_power_2700 (R : Law (CleanPair × CleanPair))
    (hR : IsCoupling R cleanWithin cleanBetween) :
    (19 : ℝ) / 20 ≤ probability (iid R 2700)
      (fun z => Rejects (fun i => cleanAgreement (z i).1 - cleanAgreement (z i).2)) :=
  coupling_power_2700 R cleanWithin cleanBetween hR clean_agreement_binary
    clean_agreement_binary clean_marginal_gap

theorem common_clean_coupling_size (P : Law CleanPair) (R : Law (CleanPair × CleanPair))
    (hR : IsCoupling R P P) (N : ℕ) :
    probability (iid R N)
      (fun z => Rejects (fun i => cleanAgreement (z i).1 - cleanAgreement (z i).2)) ≤
      (1 : ℝ) / 20 :=
  coupling_null_size R P P hR clean_agreement_binary clean_agreement_binary rfl N

end Rhone.Statistics.DependentPairedTest
