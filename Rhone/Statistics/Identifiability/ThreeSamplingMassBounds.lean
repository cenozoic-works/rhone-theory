/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingJointLaw
public import Rhone.Statistics.Identifiability.ACFluxMassBound

/-! # Finite-mass bounds without any source or post-pair properness assumption -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability
namespace PairIntegrable

lemma exitDensity_lintegral_le_one (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) ≤ 1 := by
  have he := ac_flux_lintegral_le_initial
    (fun b _ => survival_ac k c q hc hq s s b i)
    (fun t ht => survival_nonnegative k c q hc hq hqn hs ht i) (by
      filter_upwards [survival_derivative_ae k c q hc hq] with t ht _
      exact ht s i) (exitDensity_nonnegative_ae k c q hc hq hcn hqn hs i)
    (exitDensity_locallyIntegrable k c q hc hq s i).aestronglyMeasurable.aemeasurable.restrict
  simpa only [survival_self k c q hc hq s i, ENNReal.ofReal_one] using he

end PairIntegrable
namespace ThreeSampling

lemma firstLaw_mass_le_one (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    firstLaw ρ k c q univ ≤ 1 := by
  have he := ac_flux_lintegral_le_initial (fun b _ => survival_ac ρ k c q hc hq 0 b)
    (fun t ht => (survival_positive ρ k c q hρ hρsum hc hq hqn ht).le) (by
      filter_upwards [survival_derivative_ae ρ k c q hc hq] with t ht _
      simpa only [firstDensity, neg_mul] using ht)
    (firstDensity_nonnegative_ae ρ k c q hρ hc hq hcn hqn)
    (firstDensity_locallyIntegrable ρ k c q hc hq).aestronglyMeasurable.aemeasurable.restrict
  simpa only [firstLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    survival_initial ρ k c q hρsum hc hq,
    ENNReal.ofReal_one] using he

lemma jointDensity_row_lintegral_le (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {s : ℝ} (hs : 0 < s) (hcs : 0 ≤ c s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (jointDensity ρ k c q (s,t))) ≤
      ENNReal.ofReal (firstDensity ρ k c q s) := by
  have h0 := firstFlux_nonnegative_at ρ k c q hρ hc hq hqn hs.le hcs (0 : Fin 2)
  have h1 := firstFlux_nonnegative_at ρ k c q hρ hc hq hqn hs.le hcs (1 : Fin 2)
  have hn0 := PairIntegrable.exitDensity_nonnegative_ae k c q hc hq hcn hqn hs.le 0
  have hn1 := PairIntegrable.exitDensity_nonnegative_ae k c q hc hq hcn hqn hs.le 1
  have he : (∫⁻ t in Ioi s, ENNReal.ofReal (jointDensity ρ k c q (s,t))) =
      ∫⁻ t in Ioi s,
        ENNReal.ofReal (firstFlux ρ k c q s 0) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t) +
        ENNReal.ofReal (firstFlux ρ k c q s 1) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 1 t) := by
    apply lintegral_congr_ae
    filter_upwards [hn0.filter_mono (ae_mono Measure.restrict_le_self),
      hn1.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with t ht0 ht1 ht
    dsimp only [jointDensity]
    rw [Fin.sum_univ_two, ENNReal.ofReal_add (mul_nonneg h0 (ht0 ht.le))
      (mul_nonneg h1 (ht1 ht.le)), ENNReal.ofReal_mul h0, ENNReal.ofReal_mul h1]
  have hm : AEMeasurable (fun t => ENNReal.ofReal (firstFlux ρ k c q s 0) *
      ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t)) (volume.restrict (Ioi s)) := by
    have hp := PairIntegrable.exitDensity_locallyIntegrable k c q hc hq s 0
    exact aemeasurable_const.mul hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
  rw [he, lintegral_add_left' hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (firstFlux ρ k c q s 0) * 1 +
        ENNReal.ofReal (firstFlux ρ k c q s 1) * 1 :=
      add_le_add (mul_le_mul_right (PairIntegrable.exitDensity_lintegral_le_one
        k c q hc hq hcn hqn hs.le 0) _) (mul_le_mul_right
        (PairIntegrable.exitDensity_lintegral_le_one k c q hc hq hcn hqn hs.le 1) _)
    _ = _ := by
      rw [mul_one, mul_one, ← ENNReal.ofReal_add h0 h1]
      congr 1
      simpa only [Fin.sum_univ_two] using firstFlux_sum ρ k c q s

end ThreeSampling
end Rhone.Statistics.Identifiability
