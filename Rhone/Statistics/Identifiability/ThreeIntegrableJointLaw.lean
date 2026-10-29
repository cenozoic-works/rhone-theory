/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableFirstLaw
public import Rhone.Statistics.Identifiability.ThreeIntegrableKernel
public import Rhone.Statistics.Identifiability.PairIntegrableExit
public import Rhone.Statistics.Identifiability.PairIntegrableProperness

/-! # Row integrals and first marginal of the integrable three-sample joint law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma jointDensity_row_lintegral (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {s : ℝ} (hs : 0 < s) (hcs : 0 ≤ c s)
    (htail : ∀ i, Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (jointDensity k c q (s,t))) =
      ENNReal.ofReal (firstDensity k c q s) := by
  have h0 := firstFlux_nonnegative_at k c q hc hq hqn hs.le hcs (0 : Fin 2)
  have h1 := firstFlux_nonnegative_at k c q hc hq hqn hs.le hcs (1 : Fin 2)
  have hn0 := PairIntegrable.exitDensity_nonnegative_ae k c q hc hq hcn hqn hs.le 0
  have hn1 := PairIntegrable.exitDensity_nonnegative_ae k c q hc hq hcn hqn hs.le 1
  have he : (∫⁻ t in Ioi s, ENNReal.ofReal (jointDensity k c q (s,t))) =
      ∫⁻ t in Ioi s,
        ENNReal.ofReal (firstFlux k c q s 0) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t) +
        ENNReal.ofReal (firstFlux k c q s 1) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 1 t) := by
    apply lintegral_congr_ae
    filter_upwards [hn0.filter_mono (ae_mono Measure.restrict_le_self),
      hn1.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with t ht0 ht1 ht
    dsimp only [jointDensity]
    rw [Fin.sum_univ_two, ENNReal.ofReal_add (mul_nonneg h0 (ht0 ht.le))
      (mul_nonneg h1 (ht1 ht.le)), ENNReal.ofReal_mul h0, ENNReal.ofReal_mul h1]
  have hm : AEMeasurable (fun t => ENNReal.ofReal (firstFlux k c q s 0) *
      ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t)) (volume.restrict (Ioi s)) := by
    have hp := PairIntegrable.exitDensity_locallyIntegrable k c q hc hq s 0
    exact aemeasurable_const.mul hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
  rw [he, lintegral_add_left' hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    PairIntegrable.exitDensity_lintegral_one k c q hc hq hcn hqn hs.le 0 (htail 0),
    PairIntegrable.exitDensity_lintegral_one k c q hc hq hcn hqn hs.le 1 (htail 1),
    mul_one, mul_one, ← ENNReal.ofReal_add h0 h1]
  congr 1
  simpa only [Fin.sum_univ_two] using firstFlux_sum k c q s

lemma law_first_marginal (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (law k c q).map Prod.fst = firstLaw k c q := by
  rw [law, triangular_map_fst_ae _ (jointDensity_aemeasurable k c q hc hq)]
  apply withDensity_congr_ae
  filter_upwards [hcn.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with s hcs hs
  exact jointDensity_row_lintegral k c q hc hq hcn hqn hs (hcs hs.le) (hpair s hs.le)

lemma law_probability_initial_proper (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    IsProbabilityMeasure (law k c q) := by
  constructor
  rw [law, triangularDensityLaw_mass_of_tail_ae (jointDensity k c q) (firstDensity k c q)
    (jointDensity_aemeasurable k c q hc hq)]
  · exact firstDensity_lintegral_one k c q hc hq hcn hqn hproper
  · filter_upwards [hcn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with s hcs hs
    exact jointDensity_row_lintegral k c q hc hq hcn hqn hs (hcs hs.le)
      (PairIntegrable.all_pair_tails_of_initial_proper k c q hc hq hqn hproper hA hQ s)

end Rhone.Statistics.Identifiability.ThreeIntegrable
