/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleRootFreePolynomial
public import Rhone.Statistics.Identifiability.ThreeIntegrableCDFSeparation
public import Rhone.Statistics.Identifiability.ThreeIntegrableHalfLine

/-! # A root-free polynomial in three observable genealogy-event probabilities -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace ThreeSampleCDF

lemma firstSurvival_nonnegative (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (t : ℝ) :
    0 ≤ firstSurvival μ t := by
  let : IsProbabilityMeasure (μ.map Prod.fst) :=
    inferInstance
  exact sub_nonneg.mpr measureReal_le_one

def rootFreeStatistic (μ : Measure (ℝ × ℝ)) (s t : ℝ) : ℝ :=
  ThreeSampleRootFree.eventPolynomial (firstSurvival μ s) (firstSurvival μ t)
    (μ.real (Ioc 0 s ×ˢ Ioi t))

theorem rootFreeStatistic_zero_iff (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (s t : ℝ) : rootFreeStatistic μ s t = 0 ↔ rectangleResidual μ s t = 0 := by
  unfold rootFreeStatistic
  rw [ThreeSampleRootFree.eventPolynomial_zero_iff _ _ _
    (firstSurvival_nonnegative μ s) (firstSurvival_nonnegative μ t)]
  unfold rectangleResidual clockRoot
  exact sub_eq_zero.symm

theorem pan_rootFreeStatistic_zero_halfLine (rate : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rootFreeStatistic (PanThreeSample.law rate) s t = 0 := by
  let : IsProbabilityMeasure (PanThreeSample.law rate) :=
    PanThreeSample.law_probability_halfLine rate hr hn htail
  exact (rootFreeStatistic_zero_iff _ s t).mpr
    (pan_rectangleResidual_zero_halfLine rate hr hn htail hs hst)

end ThreeSampleCDF
namespace ThreeIntegrable
open ThreeTimeVarying

theorem halfLine_exists_nonzero_rootFreeStatistic (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrableOn c (Ici 0) volume) (hq : LocallyIntegrableOn q (Ici 0) volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k (panZeroExtension c) (panZeroExtension q) 0 0)
      atTop (𝓝 0)) (hMigration : ¬ ∀ᵐ t, 0 ≤ t → q t = 0) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧
      ThreeSampleCDF.rootFreeStatistic
        (law k (panZeroExtension c) (panZeroExtension q)) s t ≠ 0 := by
  have hc' := panZeroExtension_locallyIntegrable hc
  have hq' := panZeroExtension_locallyIntegrable hq
  have hcn' := extension_nonnegative_ae c hcn
  have hqn' := extension_nonnegative_ae q hqn
  obtain ⟨A, hA, hQ⟩ := IntegrableExposure.exists_positive_exposure_of_not_ae_zero
    (panZeroExtension q) hq' hqn'
    (fun h => hMigration ((extension_ae_zero_iff q).mp h))
  obtain ⟨s, t, hs, hst, hne⟩ := exists_nonzero_rectangleResidual k
    (panZeroExtension c) (panZeroExtension q) hc' hq' hcn' hqn' hproper hA hQ
  let : IsProbabilityMeasure (law k (panZeroExtension c) (panZeroExtension q)) :=
    law_probability k (panZeroExtension c) (panZeroExtension q) hc' hq' hcn' hqn' hproper
  exact ⟨s, t, hs, hst, fun h => hne ((ThreeSampleCDF.rootFreeStatistic_zero_iff _ s t).mp h)⟩

end ThreeIntegrable
end Rhone.Statistics.Identifiability
