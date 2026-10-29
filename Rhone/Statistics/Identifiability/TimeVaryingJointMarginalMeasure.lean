/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingPairMarginal

/-! # Coordinate marginals of the time-dependent diagonal/triangular law -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Matrix
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem density_lintegral_upperWedge_snd (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in upperWedge, f p ∂planeVolume) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo 0 t, f (s,t) := by
  rw [← lintegral_indicator upperWedge_open.measurableSet]
  change (∫⁻ p, upperWedge.indicator f p ∂(volume : Measure ℝ).prod volume) = _
  rw [lintegral_prod_symm _ (hf.indicator upperWedge_open.measurableSet).aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
      ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro s
    simp [upperWedge, Set.indicator]
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    have hz : (fun s => upperWedge.indicator f (s,t)) = fun _ => 0 := by
      funext s
      have hs : ¬ (0 < s ∧ s < t) := by rintro ⟨h₁,h₂⟩; exact ht (h₁.trans h₂)
      simp [upperWedge, hs]
    rw [hz, lintegral_zero]

theorem triangularDensityLaw_map_fst (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map Prod.fst =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ∫⁻ t in Ioi s, ENNReal.ofReal (j (s, t))) := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB, triangularDensityLaw,
    withDensity_apply _ (hB.preimage measurable_fst),
    ← lintegral_indicator (hB.preimage measurable_fst),
    density_lintegral_upperWedge _
      (hj.ennreal_ofReal.indicator (hB.preimage measurable_fst)),
    withDensity_apply _ hB, ← lintegral_indicator hB]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ B
  · simp [Set.indicator, hs]
  · simp [Set.indicator, hs]

theorem triangularDensityLaw_map_snd (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map Prod.snd =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s, t))) := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB, triangularDensityLaw,
    withDensity_apply _ (hB.preimage measurable_snd),
    ← lintegral_indicator (hB.preimage measurable_snd),
    density_lintegral_upperWedge_snd _
      (hj.ennreal_ofReal.indicator (hB.preimage measurable_snd)),
    withDensity_apply _ hB, ← lintegral_indicator hB]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ B
  · simp [Set.indicator, ht]
  · simp [Set.indicator, ht]

theorem diagonalDensityLaw_map_snd (δ : ℝ → ℝ) :
    (diagonalDensityLaw δ).map Prod.snd =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (δ t)) := by
  rw [diagonalDensityLaw,Measure.map_map (f := fun t : ℝ => (t,t))
    measurable_snd (measurable_id.prodMk measurable_id)]
  change Measure.map id _ = _
  rw [Measure.map_id]

theorem triangularDensityLaw_map_fst_of_tail (j : ℝ × ℝ → ℝ) (b : ℝ → ℝ)
    (hj : Measurable j)
    (htail : ∀ s, 0 < s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (j (s, t))) = ENNReal.ofReal (b s)) :
    (triangularDensityLaw j).map Prod.fst =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (b s)) := by
  rw [triangularDensityLaw_map_fst j hj]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact htail s hs

theorem asymmetricDensityLaw_map_snd (δ b : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hδ : Measurable δ) (hb : Measurable b)
    (hjA : Measurable jA) (hjB : Measurable jB)
    (htail : ∀ s, 0 < s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (jB (s, t))) = ENNReal.ofReal (b s)) :
    (diagonalDensityLaw δ + triangularDensityLaw jA +
      (triangularDensityLaw jB).map Prod.swap).map Prod.snd =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t =>
        ENNReal.ofReal (δ t) + ENNReal.ofReal (b t) +
        ∫⁻ s in Ioo 0 t, ENNReal.ofReal (jA (s, t))) := by
  rw [Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
    diagonalDensityLaw_map_snd, triangularDensityLaw_map_snd jA hjA,
    Measure.map_map (f := Prod.swap) measurable_snd (measurable_snd.prodMk measurable_fst)]
  change _ + (triangularDensityLaw jB).map Prod.fst = _
  rw [triangularDensityLaw_map_fst_of_tail jB b hjB htail]
  rw [add_assoc, add_comm ((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ∫⁻ s in Ioo 0 t, ENNReal.ofReal (jA (s, t)))), ← add_assoc]
  rw [← withDensity_add_left hδ.ennreal_ofReal,
    ← withDensity_add_left (hδ.ennreal_ofReal.add hb.ennreal_ofReal)]
  rfl

theorem lintegral_ofReal_upperDensity_eq_intervalIntegral (j : ℝ × ℝ → ℝ)
    (hj : Continuous j) (hjn : ∀ p ∈ upperWedge, 0 ≤ j p) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s, t))) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..t, j (s,t)) := by
  rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact ((hj.comp (continuous_id.prodMk continuous_const)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hjn (s,t) hs

theorem timeVaryingJointLaw_map_snd (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (timeVaryingJointLaw k c q r).map Prod.snd = timeVaryingPairExitLaw k c q 0 0 := by
  obtain ⟨hδ, hA, hB⟩ := timeVaryingJointDensities_continuous k c q r hc hq hr
  obtain ⟨hδn, hAn, _hBn⟩ := timeVaryingJointDensities_nonneg k c q r hc hq hr hcn hqn hrn
  rw [timeVaryingJointLaw,
    asymmetricDensityLaw_map_snd _ (timeVaryingBranchFlux k c q r 3 4) _ _
      hδ.measurable (timeVaryingBranchFlux_continuous k c q r hc hq hr 3 4).measurable
      hA.measurable hB.measurable
      (fun s hs => timeVaryingBranchDensity_lintegral k c q r hc hq hr hcn hqn hrn
        hs.le 3 4 (hpair s hs.le)),
    timeVaryingPairExitLaw]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hb := timeVaryingBranchFlux_nonneg k c q r hc hq hr hcn hqn hrn ht.le 3 4
  have hi : 0 ≤ ∫ s in (0 : ℝ)..t, timeVaryingUpperDensity k c q r (s,t) := by
    apply intervalIntegral.integral_nonneg ht.le
    intro s hs
    exact timeVaryingBranchDensity_nonneg k c q r hc hq hr hcn hqn hrn hs.1 hs.2 1 2
  rw [lintegral_ofReal_upperDensity_eq_intervalIntegral _ hA hAn ht.le,
    ← ENNReal.ofReal_add (hδn t ht.le) hb,
    ← ENNReal.ofReal_add (add_nonneg (hδn t ht.le) hb) hi,
    timeVaryingJoint_marginal_density k c q r hc hq hr t]

theorem regularJointLaw_map_fst_eq_snd (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ) :
    (regularJointLaw δ j).map Prod.fst = (regularJointLaw δ j).map Prod.snd := by
  rw [regularJointLaw, Measure.map_add _ _ measurable_fst,
    Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_snd,
    Measure.map_add _ _ measurable_snd,
    diagonalDensityLaw_map_fst, diagonalDensityLaw_map_snd,
    Measure.map_map (f := Prod.swap) measurable_fst (measurable_snd.prodMk measurable_fst),
    Measure.map_map (f := Prod.swap) measurable_snd (measurable_snd.prodMk measurable_fst)]
  change _ + (triangularDensityLaw j).map Prod.snd =
    _ + (triangularDensityLaw j).map Prod.fst
  ac_rfl

theorem timeVaryingJointLaw_map_fst (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (timeVaryingJointLaw k c q r).map Prod.fst = timeVaryingPairExitLaw k c q 0 0 := by
  rw [timeVaryingJointLaw_eq_regular k c q r hc hq hr, regularJointLaw_map_fst_eq_snd,
    ← timeVaryingJointLaw_eq_regular k c q r hc hq hr]
  exact timeVaryingJointLaw_map_snd k c q r hc hq hr hcn hqn hrn hpair

end Rhone.Statistics.Identifiability
