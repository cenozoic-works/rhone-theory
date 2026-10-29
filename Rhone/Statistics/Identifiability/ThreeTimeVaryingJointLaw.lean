/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingFirstLaw
public import Rhone.Statistics.Identifiability.ProperInitialOnsetSeparation
public import Rhone.Statistics.Identifiability.AEDensityMarginals

/-! # Literal ordered first/root law, exact first marginal, and probability normalization -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def law (k : ℕ) (c q : ℝ → ℝ) : Measure (ℝ × ℝ) := triangularDensityLaw (jointDensity k c q)

lemma jointDensity_row_lintegral (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s : ℝ} (hs : 0 < s)
    (htail : ∀ i, Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (jointDensity k c q (s,t))) =
      ENNReal.ofReal (firstDensity k c q s) := by
  have h0 := firstFlux_nonnegative k c q hc hq hcn hqn hs.le (0 : Fin 2)
  have h1 := firstFlux_nonnegative k c q hc hq hcn hqn hs.le (1 : Fin 2)
  have he : (∫⁻ t in Ioi s, ENNReal.ofReal (jointDensity k c q (s,t))) =
      ∫⁻ t in Ioi s,
        ENNReal.ofReal (firstFlux k c q s 0) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t) +
        ENNReal.ofReal (firstFlux k c q s 1) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 1 t) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [jointDensity]
    rw [Fin.sum_univ_two, ENNReal.ofReal_add
      (mul_nonneg h0 (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs.le ht.le 0))
      (mul_nonneg h1 (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs.le ht.le 1)),
      ENNReal.ofReal_mul h0, ENNReal.ofReal_mul h1]
  have hpost : Continuous (fun t => timeVaryingPairExitDensity k c q s 0 t) :=
    (timeVaryingPairExitDensity_continuous k c q hc hq 0).comp
      (continuous_const.prodMk continuous_id)
  have hm : Measurable (fun t => ENNReal.ofReal (firstFlux k c q s 0) *
      ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t)) :=
    measurable_const.mul hpost.measurable.ennreal_ofReal
  rw [he, lintegral_add_left hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    timeVaryingPairExitDensity_lintegral_one k c q hc hq hcn hqn hs.le 0 (htail 0),
    timeVaryingPairExitDensity_lintegral_one k c q hc hq hcn hqn hs.le 1 (htail 1),
    mul_one, mul_one, ← ENNReal.ofReal_add h0 h1]
  congr 1
  simpa only [Fin.sum_univ_two] using firstFlux_sum k c q s

theorem law_first_marginal (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (law k c q).map Prod.fst = firstLaw k c q := by
  rw [law, triangular_map_fst _ (jointDensity_continuous k c q hc hq).measurable]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact jointDensity_row_lintegral k c q hc hq hcn hqn hs (hpair s hs.le)

theorem law_probability_initial_proper (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hQ : 0 < ∫ u in (0 : ℝ)..a, q u) :
    IsProbabilityMeasure (law k c q) := by
  constructor
  rw [law, triangularDensityLaw_mass_of_tail_ae (jointDensity k c q) (firstDensity k c q)
    (jointDensity_continuous k c q hc hq).measurable.aemeasurable]
  · exact firstDensity_lintegral_one k c q hc hq hcn hqn hproper
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact jointDensity_row_lintegral k c q hc hq hcn hqn hs
      (PairProperness.all_pair_tails_of_initial_proper k c q hc hq hqn hproper ha hQ s)

end Rhone.Statistics.Identifiability.ThreeTimeVarying
