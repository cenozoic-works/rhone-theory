/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RankAE
public import Rhone.Statistics.Identifiability.DensityPositive
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Measure-level separation on a rectangle above the time diagonal -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable abbrev timeBoxMeasure : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Ioo 0 1)).prod ((volume : Measure ℝ).restrict (Ioi 1))

noncomputable def upperBoxLaw (k : Nat) (c q r : ℝ) : Measure (ℝ × ℝ) :=
  timeBoxMeasure.withDensity (fun p => ENNReal.ofReal (upperDensity k c q r p.1 p.2))

theorem upperBoxLaw_ne_product_density (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t) :
    upperBoxLaw k c q r ≠
      timeBoxMeasure.withDensity (fun p => ENNReal.ofReal (a p.1 * b p.2)) := by
  intro heq
  have hd := (withDensity_eq_iff_of_sigmaFinite
    (upperDensity_continuous k c q r).measurable.ennreal_ofReal.aemeasurable
    ((ha.comp measurable_fst).mul (hb.comp measurable_snd)).ennreal_ofReal.aemeasurable).mp heq
  have hm : ∀ᵐ p ∂timeBoxMeasure, p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioi (1 : ℝ) := by
    change ∀ᵐ p ∂((volume : Measure ℝ).restrict (Ioo 0 1)).prod
      ((volume : Measure ℝ).restrict (Ioi 1)), p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi (1 : ℝ)
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioi)
  apply no_ae_rank_one_density k hc hq hr
  refine ⟨a,b,?_⟩
  filter_upwards [hd, hm] with p hp hmem
  exact (ENNReal.ofReal_eq_ofReal_iff
    (upperDensity_nonneg k hc.le hq.le hr.le hmem.1.1.le
      (le_trans hmem.1.2.le (show 1 ≤ p.2 from hmem.2.le)))
    (mul_nonneg (ha0 p.1) (hb0 p.2))).mp hp

end Rhone.Statistics.Identifiability
