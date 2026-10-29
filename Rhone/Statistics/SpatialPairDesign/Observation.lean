/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SpatialPairDesign.Laplace
public import Rhone.Statistics.PairObservationChannel.Observation
public import Rhone.Statistics.PairObservationChannel.Identity
public import Rhone.Statistics.LinkedPairMoments.Expansion

/-! # Shared-observer bridge for the symmetric-island absorption measures -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.SpatialPairDesign
open DependenceBudget PairObservationChannel MarkovChain.Identifiability Identifiability
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def sourceLaw (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) (i : Fin 2) : Law (H × H) := by
  letI := pair_law_probability n hc hq i
  exact reportedLaw E (pairLaplace (pairLaw n c q i) k)
    (pair_laplace_bounds _ hk ((pair_law_positive_support n c q i).mono (fun _ h => h.le)))

theorem sourceLaw_mass (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) (i : Fin 2) (x y : H) :
    (sourceLaw E n hc hq hk i).mass (x, y) = observedMass E (pairLaw n c q i) k x y := by
  let : IsProbabilityMeasure (pairLaw n c q i) := pair_law_probability n hc hq i
  exact (observed_mass_formula E _ hk
    ((pair_law_positive_support n c q i).mono (fun _ h => h.le)) x y).symm

theorem source_agreement_gap [DecidableEq H] (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) :
    rejection (sourceLaw E n hc hq hk 0) (fun xy => if xy.1 = xy.2 then 1 else 0) -
      rejection (sourceLaw E n hc hq hk 1) (fun xy => if xy.1 = xy.2 then 1 else 0) =
      retainedVariance E * (c * k / pairLaplaceDenominator n c q k) := by
  rw [sourceLaw, sourceLaw, agreement_as_expectation, agreement_as_expectation,
    agreement_gap, pairLaplace_gap n hc hq hk]

theorem source_separated_iff (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) :
    sourceLaw E n hc hq hk.le 0 ≠ sourceLaw E n hc hq hk.le 1 ↔ Informative E := by
  classical
  have hgap : 0 < c * k / pairLaplaceDenominator n c q k :=
    div_pos (mul_pos hc hk) (pairLaplaceDenominator_pos n hc hq hk.le)
  constructor
  · intro hne
    by_contra hE
    have hv : retainedVariance E = 0 := le_antisymm
      (le_of_not_gt (fun h => hE ((retained_variance_pos_iff E).mp h)))
      (retained_variance_nonneg E)
    apply hne
    apply LinkedPairMoments.finite_law_ext
    intro x
    exact (reported_mass_eq_iff E _ _).mpr (Or.inr hv) x.1 x.2
  · intro hE he
    have h := source_agreement_gap E n hc hq hk.le
    rw [he, sub_self] at h
    have hp := mul_pos ((retained_variance_pos_iff E).mpr hE) hgap
    linarith

theorem clean_agreement_gap :
    rejection (sourceLaw (identityChannel 4 (by norm_num)) 0 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (0 : ℝ) ≤ 2) 0)
      (fun xy => if xy.1 = xy.2 then 1 else 0) -
    rejection (sourceLaw (identityChannel 4 (by norm_num)) 0 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (0 : ℝ) ≤ 2) 1)
      (fun xy => if xy.1 = xy.2 then 1 else 0) = (15 : ℝ) / 61 := by
  rw [source_agreement_gap, identity_variance]
  norm_num [pairLaplaceDenominator]

end Rhone.Statistics.SpatialPairDesign
