/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IslandThreeFirstMarginal
public import Rhone.Statistics.Identifiability.PanThreeSampleLaw

/-! # One positive mutation clock separates three-sample count laws -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Rhone.Statistics.Identifiability

namespace PanThreeSample
def countLaw (mutationRate : ℝ) (rate : ℝ → ℝ) : Measure (ℕ × ℕ) :=
  ThreeSampleCounts.law mutationRate (durationLaw rate)

theorem countLaw_probability (mutationRate : ℝ) (rate : ℝ → ℝ)
    (hmutation : 0 ≤ mutationRate) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    IsProbabilityMeasure (countLaw mutationRate rate) := by
  let : IsProbabilityMeasure (durationLaw rate) := durationLaw_probability rate hr hn htail
  exact ThreeSampleCounts.law_isProbability _ (durationLaw_nonnegative rate) hmutation
end PanThreeSample

theorem island_three_countLaw_ne_pan_countLaw (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop) :
    IslandThreeTimes.countLaw k c q mutationRate ≠ PanThreeSample.countLaw mutationRate rate := by
  intro hcount
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw k c q) :=
    IslandThreeTimes.durationLaw_probability k hc hq
  let : IsProbabilityMeasure (PanThreeSample.durationLaw rate) :=
    PanThreeSample.durationLaw_probability rate hr hn htail
  have htimes : IslandThreeTimes.durationLaw k c q = PanThreeSample.durationLaw rate :=
    ThreeSampleCounts.law_injective _ _ (IslandThreeTimes.durationLaw_nonnegative k c q)
      (PanThreeSample.durationLaw_nonnegative rate) hmutation hcount
  have hfirst : firstExitLaw (threeGenerator k c q) 0 =
      panPairLaw (fun t => 3*rate t) := by
    rw [← IslandThreeTimes.durationLaw_map_first k hc hq, htimes]
    exact PanThreeSample.durationLaw_first_marginal rate hr hn htail
  have hroot : firstExitLaw (islandThreeTreeGenerator k c q) 0 =
      (PanThreeSample.durationLaw rate).map (fun p => p.1+p.2) := by
    rw [← IslandThreeTimes.durationLaw_map_root k hc.le hq.le, htimes]
  have h3rate : LocallyIntegrable (fun t => 3*rate t) volume := by
    convert! hr.smul (3 : ℝ) using 1
  apply threeWitness_not_zero_on_unit_interval k hc hq
  intro t ht
  have h3 : threeSurvivalJet k c q 0 t = Real.exp (-3 * integratedClock rate t) := by
    have h := threeLaw_survival_CDF k hc.le hq.le ht.1
    rw [hfirst, panPairLaw_real_Ioc _ h3rate
      (fun s => mul_nonneg (by norm_num) (hn s)) ht.1, integratedClock_scale] at h
    simpa [neg_mul] using h.symm
  have h5 : flowOutput (islandThreeTreeGenerator k c q) 0 (fun _ => 1) 0 t =
      (3/2 : ℝ) * Real.exp (-integratedClock rate t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate t) := by
    have h := firstExitLaw_real_Ioc (islandThreeTreeGenerator k c q)
      (islandThreeTree_metzler k hc.le hq.le) (islandThreeTree_rows_nonpos k hc.le) 0 ht.1
    rw [hroot, PanThreeSample.durationLaw_root_cdf rate hr hn ht.1] at h
    linarith
  have hpair : survivalJet k c q 0 t = Real.exp (-integratedClock rate t) := by
    rw [island_pair_first_root_survival_identity, h3, h5]
    ring
  have hcube : Real.exp (-integratedClock rate t)^3 =
      Real.exp (-3 * integratedClock rate t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [threeWitness, h3, hpair, hcube, sub_self]

theorem island_three_counts_no_size_history_match (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate) :
    ¬ ∃ rate : ℝ → ℝ, LocallyIntegrable rate volume ∧ (∀ t, 0 ≤ rate t) ∧
      Tendsto (integratedClock rate) atTop atTop ∧
      IslandThreeTimes.countLaw k c q mutationRate = PanThreeSample.countLaw mutationRate rate := by
  rintro ⟨rate,hr,hn,htail,heq⟩
  exact island_three_countLaw_ne_pan_countLaw k hc hq hmutation rate hr hn htail heq

end Rhone.Statistics.Identifiability
