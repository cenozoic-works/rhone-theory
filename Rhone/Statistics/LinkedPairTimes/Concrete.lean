/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairTimes.Mixture
public import Rhone.Statistics.LinkedPairTimes.Moments
public import Rhone.Statistics.PairObservationChannel.Identity
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting

/-! # Continuous-law example and independent/coupled fixed-test endpoints -/

@[expose] public section

namespace Rhone.Statistics.LinkedPairTimes
open DependenceBudget DependentPairedTest PairObservationChannel
open LinkedPairMoments LinkedAgreementPower

abbrev PairPanel := Fin 2 → Fin 4 × Fin 4

noncomputable def simplePanel : Law PairPanel :=
  panelLaw (identityChannel 4 (by norm_num)) simpleTime (by norm_num : (0 : ℝ) ≤ 1)
    simple_nonnegative 2

noncomputable def mixturePanel : Law PairPanel :=
  panelLaw (identityChannel 4 (by norm_num)) mixtureTime (by norm_num : (0 : ℝ) ≤ 1)
    mixture_nonnegative 2

theorem simple_agreement_mean : rejection simplePanel allAgreement = (7 : ℝ) / 16 := by
  rw [simplePanel, two_agreement_mean, identity_baseline, identity_variance,
    simple_laplace (by norm_num), simple_laplace (by norm_num)]
  norm_num

theorem mixture_agreement_mean : rejection mixturePanel allAgreement = (143 : ℝ) / 320 := by
  rw [mixturePanel, two_agreement_mean, identity_baseline, identity_variance,
    mixture_laplace (by norm_num), mixture_laplace (by norm_num)]
  norm_num

theorem linked_gap :
    rejection mixturePanel allAgreement - rejection simplePanel allAgreement = (3 : ℝ) / 320 := by
  rw [mixture_agreement_mean, simple_agreement_mean]
  norm_num

theorem one_site_tie (E : Channel 4 (Fin 4)) :
    panelLaw E simpleTime (by norm_num : (0 : ℝ) ≤ 1) simple_nonnegative 1 =
      panelLaw E mixtureTime (by norm_num : (0 : ℝ) ≤ 1) mixture_nonnegative 1 := by
  apply panel_eq_of_moments
  intro r hr
  interval_cases r
  · simp [pairLaplace]
  · simpa using first_laplace_tie

theorem two_site_separation : mixturePanel ≠ simplePanel := by
  intro he
  have hg := linked_gap
  rw [he, sub_self] at hg
  norm_num at hg

theorem independent_linked_power_900000 :
    (19 : ℝ) / 20 ≤ independentTest mixturePanel simplePanel allAgreement 900000 := by
  apply binary_signed_power _ _ (all_agreement_binary 2) 900000
  · rw [mixture_agreement_mean, simple_agreement_mean]
    norm_num
  · rw [mixture_agreement_mean, simple_agreement_mean]
    norm_num

theorem coupling_linked_power_1821000 (R : Law (PairPanel × PairPanel))
    (hR : IsCoupling R mixturePanel simplePanel) :
    (19 : ℝ) / 20 ≤ probability (iid R 1821000)
      (fun z => Rejects (fun i => allAgreement (z i).1 - allAgreement (z i).2)) := by
  apply coupling_worst_discordance_power R mixturePanel simplePanel hR
    (all_agreement_binary 2) (all_agreement_binary 2) 1821000
  rw [linked_gap]
  norm_num

theorem common_linked_coupling_size (P : Law PairPanel) (R : Law (PairPanel × PairPanel))
    (hR : IsCoupling R P P) (N : ℕ) :
    probability (iid R N)
      (fun z => Rejects (fun i => allAgreement (z i).1 - allAgreement (z i).2)) ≤ (1 : ℝ) / 20 :=
  coupling_null_size R P P hR (all_agreement_binary 2) (all_agreement_binary 2) rfl N

end Rhone.Statistics.LinkedPairTimes
