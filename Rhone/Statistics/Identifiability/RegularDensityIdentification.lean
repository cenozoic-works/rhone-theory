/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularJointLaw
public import Rhone.Statistics.Identifiability.AEWitness

/-! # Continuous nonnegative component densities are identified by the joint measure -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem regularJointLaw_identifies_diagonal {δ₁ δ₂ : ℝ → ℝ} {j₁ j₂ : ℝ × ℝ → ℝ}
    (hδ₁ : Continuous δ₁) (hδ₂ : Continuous δ₂)
    (hn₁ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ δ₁ t) (hn₂ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ δ₂ t)
    (he : regularJointLaw δ₁ j₁ = regularJointLaw δ₂ j₂) : EqOn δ₁ δ₂ (Ioi 0) := by
  have hr := congrArg (fun μ : Measure (ℝ × ℝ) => μ.restrict timeDiagonal) he
  rw [regularJointLaw_restrict_diagonal,regularJointLaw_restrict_diagonal] at hr
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) hr
  rw [diagonalDensityLaw_map_fst,diagonalDensityLaw_map_fst] at hm
  have ha := (withDensity_eq_iff_of_sigmaFinite hδ₁.measurable.ennreal_ofReal.aemeasurable
    hδ₂.measurable.ennreal_ofReal.aemeasurable).mp hm
  have hreal : δ₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] δ₂ := by
    filter_upwards [ha,ae_restrict_mem measurableSet_Ioi] with t ht hpos
    exact (ENNReal.ofReal_eq_ofReal_iff (hn₁ t hpos) (hn₂ t hpos)).mp ht
  exact Measure.eqOn_open_of_ae_eq hreal isOpen_Ioi hδ₁.continuousOn hδ₂.continuousOn

theorem regularJointLaw_identifies_upper {δ₁ δ₂ : ℝ → ℝ} {j₁ j₂ : ℝ × ℝ → ℝ}
    (hj₁ : Continuous j₁) (hj₂ : Continuous j₂)
    (hn₁ : ∀ p ∈ upperWedge, 0 ≤ j₁ p) (hn₂ : ∀ p ∈ upperWedge, 0 ≤ j₂ p)
    (he : regularJointLaw δ₁ j₁ = regularJointLaw δ₂ j₂) : EqOn j₁ j₂ upperWedge := by
  have hr := congrArg (fun μ : Measure (ℝ × ℝ) => μ.restrict upperWedge) he
  rw [regularJointLaw_restrict_upper,regularJointLaw_restrict_upper] at hr
  unfold triangularDensityLaw at hr
  have ha := (withDensity_eq_iff_of_sigmaFinite hj₁.measurable.ennreal_ofReal.aemeasurable
    hj₂.measurable.ennreal_ofReal.aemeasurable).mp hr
  have hreal : j₁ =ᵐ[planeVolume.restrict upperWedge] j₂ := by
    filter_upwards [ha,ae_restrict_mem upperWedge_open.measurableSet] with p hp hpos
    exact (ENNReal.ofReal_eq_ofReal_iff (hn₁ p hpos) (hn₂ p hpos)).mp hp
  exact Measure.eqOn_open_of_ae_eq hreal upperWedge_open hj₁.continuousOn hj₂.continuousOn

end Rhone.Statistics.Identifiability
