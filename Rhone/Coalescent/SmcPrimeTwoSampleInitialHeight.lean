/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSamplePathInvariant
public import Rhone.Coalescent.SmcPrimeKingmanRootHeightLength
public import Rhone.Coalescent.SmcPrimeGenealogyLaw

/-!
# Root height of the initial tree of two samples

Source: kingman1982, eq. (1.7), (1.12); marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

theorem expMeasure_one_lintegral (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ t, f t ∂expMeasure 1 = ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-t)) * f t := by
  have hd : expMeasure 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ENNReal.ofReal (Real.exp (-t))) := by
    change volume.withDensity (exponentialPDF 1) = _
    rw [← withDensity_indicator measurableSet_Ioi]
    apply withDensity_congr_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
    rw [exponentialPDF_eq]
    by_cases hp : 0 < x
    · simp [Set.indicator_of_mem, hp, hp.le]
    · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
      simp [Set.indicator_of_notMem, hp, not_le.mpr hn]
  rw [hd, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  rfl

/-- Source: kingman1982, eq. (1.7), (1.12). -/
theorem kingmanTreeLaw_two_rootHeight_lintegral (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ T, g (rootHeight T) ∂kingmanTreeLaw 2 =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h := by
  let G : ℝ≥0∞ → ℝ≥0∞ := fun x => g x.toReal
  have hG : Measurable G := hg.comp ENNReal.measurable_toReal
  let Φ : (Fin (2 - 1) → ℝ) → ℝ≥0∞ := fun v => ∑ j, ENNReal.ofReal (v j)
  have hΦ : Measurable Φ := Finset.measurable_sum _ fun j _ =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply j)
  have hroot : Measurable fun T : Tree 2 => ENNReal.ofReal (rootHeight T) :=
    ENNReal.measurable_ofReal.comp (rootHeight_measurable 2)
  have hL : (kingmanTreeLaw 2).map (fun T => ENNReal.ofReal (rootHeight T)) =
      ((kingmanHistoryLaw 2).map (kingmanWaitingTimes 2)).map Φ := by
    rw [kingmanTreeLaw, Measure.map_map hroot (metricTreeFromHistory_measurable 2),
      Measure.map_map hΦ (kingmanWaitingTimes_measurable 2)]
    apply Measure.map_congr
    filter_upwards [kingmanHistoryLaw_supported 2] with h hs
    exact supported_rootHeight 2 h hs
  have h1 : ∫⁻ T, g (rootHeight T) ∂kingmanTreeLaw 2 =
      ∫⁻ x, G x ∂((kingmanTreeLaw 2).map fun T => ENNReal.ofReal (rootHeight T)) := by
    rw [lintegral_map hG hroot]
    refine lintegral_congr fun T => ?_
    simp only [G, ENNReal.toReal_ofReal (root_height_nonneg T)]
  have hpi : (Measure.pi fun j : Fin (2 - 1) =>
      expMeasure ((Rhone.Coalescent.coalRate (2 - j.val) : ℚ) : ℝ)) =
      Measure.pi fun _ : Fin 1 => expMeasure 1 := by
    change (Measure.pi fun j : Fin 1 =>
      expMeasure ((Rhone.Coalescent.coalRate (2 - j.val) : ℚ) : ℝ)) = _
    congr 1
    funext j
    have hj : j.val = 0 := by omega
    rw [hj]
    norm_num [Rhone.Coalescent.coalRate]
  have hmp := measurePreserving_funUnique (expMeasure 1) (Fin 1)
  have hcomp : ∀ v : Fin 1 → ℝ, G (Φ v) =
      G (ENNReal.ofReal (MeasurableEquiv.funUnique (Fin 1) ℝ v)) := by
    intro v
    change G (∑ j : Fin 1, ENNReal.ofReal (v j)) = G (ENNReal.ofReal (v default))
    rw [Fin.sum_univ_one]
    rfl
  have hGo : Measurable (fun x : ℝ => G (ENNReal.ofReal x)) :=
    hG.comp ENNReal.measurable_ofReal
  rw [h1, hL, kingmanHistoryLaw_waitingTimes, hpi, lintegral_map hG hΦ,
    lintegral_congr hcomp]
  refine (hmp.lintegral_comp hGo).trans ?_
  rw [expMeasure_one_lintegral _ hGo]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [G, ENNReal.toReal_ofReal (le_of_lt ht)]

theorem kingmanTreeLaw_two_rootHeight_pos : ∀ᵐ T ∂kingmanTreeLaw 2, 0 < rootHeight T := by
  have hg : Measurable ((Iic (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Iic
  have hlaw := kingmanTreeLaw_two_rootHeight_lintegral _ hg
  have hz : ∀ a ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-a)) *
      (Iic (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) a = (fun _ => 0) a := by
    intro a ha
    rw [indicator_of_notMem (fun hc : a ∈ Iic (0 : ℝ) => not_lt.mpr hc ha), mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hz, lintegral_zero,
    lintegral_eq_zero_iff (show Measurable (fun T : Tree 2 =>
      (Iic (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) (rootHeight T)) from
        hg.comp (rootHeight_measurable 2))] at hlaw
  filter_upwards [hlaw] with T hT
  by_contra hneg
  have hmem : rootHeight T ∈ Iic (0 : ℝ) := not_lt.mp hneg
  rw [indicator_of_mem hmem] at hT
  exact one_ne_zero hT

theorem spatialInitialLaw_two_good_ae :
    ∀ᵐ z ∂spatialInitialLaw 2, TwoSampleArray z.2 ∧ 0 < rootHeight z.2 := by
  unfold spatialInitialLaw
  rw [ae_map_iff (show Measurable (fun T : Tree 2 => ((0 : ℝ), T)) from
    measurable_const.prodMk measurable_id).aemeasurable measurableSet_twoSampleState]
  filter_upwards [kingmanTreeLaw_twoSampleArray, kingmanTreeLaw_two_rootHeight_pos]
    with T h1 h2
  exact ⟨h1, h2⟩

theorem spatialProcess_two_law_twoSampleArray_ae (R : ℝ) :
    ∀ᵐ ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2),
      ∀ n, TwoSampleArray (ω n).2 ∧ 0 < rootHeight (ω n).2 :=
  spatialProcess_law_twoSampleArray_ae R _ spatialInitialLaw_two_good_ae

theorem spatialInitialLaw_two_lintegral (Ψ : ℝ × ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, Ψ (z.1, rootHeight z.2) ∂spatialInitialLaw 2 =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * Ψ (0, h) := by
  unfold spatialInitialLaw
  rw [lintegral_map (show Measurable (fun z : SpatialState 2 => Ψ (z.1, rootHeight z.2)) from
    hΨ.comp (measurable_fst.prodMk ((rootHeight_measurable 2).comp measurable_snd)))
    (show Measurable (fun T : Tree 2 => ((0 : ℝ), T)) from
      measurable_const.prodMk measurable_id)]
  exact kingmanTreeLaw_two_rootHeight_lintegral (fun h => Ψ (0, h))
    (hΨ.comp (measurable_const.prodMk measurable_id))

end Rhone.Coalescent.SmcPrime
