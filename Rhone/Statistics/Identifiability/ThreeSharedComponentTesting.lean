/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePanelConcentration
public import Mathlib.MeasureTheory.Measure.Real

/-! # A shared subprobability component bounds distinguishability and iid testing power -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.Identifiability
namespace CommonSubmeasure
variable {Ω : Type*} [MeasurableSpace Ω]

theorem event_bound (μ ν κ : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hκμ : κ ≤ μ) (hκν : κ ≤ ν) {A : Set Ω} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ 1 - κ.real univ := by
  let : IsFiniteMeasure κ := ⟨(hκμ univ).trans_lt (measure_lt_top μ univ)⟩
  have h1 : κ.real A ≤ μ.real A := ENNReal.toReal_mono (measure_ne_top μ A) (hκμ A)
  have h2 : κ.real A ≤ ν.real A := ENNReal.toReal_mono (measure_ne_top ν A) (hκν A)
  have h3 : κ.real Aᶜ ≤ μ.real Aᶜ := ENNReal.toReal_mono (measure_ne_top μ Aᶜ) (hκμ Aᶜ)
  have h4 : κ.real Aᶜ ≤ ν.real Aᶜ := ENNReal.toReal_mono (measure_ne_top ν Aᶜ) (hκν Aᶜ)
  have hm : μ.real A + μ.real Aᶜ = 1 := by
    rw [← measureReal_union disjoint_compl_right hA.compl, union_compl_self, probReal_univ]
  have hn : ν.real A + ν.real Aᶜ = 1 := by
    rw [← measureReal_union disjoint_compl_right hA.compl, union_compl_self, probReal_univ]
  have hk : κ.real A + κ.real Aᶜ = κ.real univ := by
    rw [← measureReal_union disjoint_compl_right hA.compl, union_compl_self]
  apply abs_le.mpr
  constructor <;> linarith only [h1, h2, h3, h4, hm, hn, hk]

lemma iidLaw_mono {μ ν : Measure Ω} (h : μ ≤ ν) (N : ℕ) :
    FinitePanelSampling.iidLaw μ N ≤ FinitePanelSampling.iidLaw ν N := by
  apply Measure.le_intro
  intro A hA _
  simp only [FinitePanelSampling.iidLaw, Measure.pi, toMeasure_apply _ _ hA]
  have houter : OuterMeasure.pi (fun _ : Fin N => μ.toOuterMeasure) ≤
      OuterMeasure.pi (fun _ : Fin N => ν.toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod fun i _ => h (s i))
  exact houter A

lemma iid_mass (κ : Measure Ω) [IsFiniteMeasure κ] (N : ℕ) :
    (FinitePanelSampling.iidLaw κ N).real univ = (κ.real univ) ^ N := by
  simp [FinitePanelSampling.iidLaw, Measure.real, Measure.pi_univ, ENNReal.toReal_pow]

theorem iid_event_bound (μ ν κ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hκμ : κ ≤ μ) (hκν : κ ≤ ν) (N : ℕ) {A : Set (Fin N → Ω)} (hA : MeasurableSet A) :
    |(FinitePanelSampling.iidLaw μ N).real A - (FinitePanelSampling.iidLaw ν N).real A| ≤
      1 - (κ.real univ) ^ N := by
  let : IsFiniteMeasure κ := ⟨(hκμ univ).trans_lt (measure_lt_top μ univ)⟩
  simpa only [iid_mass] using event_bound _ _ _ (iidLaw_mono hκμ N) (iidLaw_mono hκν N) hA

theorem iid_error_sum_lower_bound (μ ν κ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hκμ : κ ≤ μ) (hκν : κ ≤ ν) (N : ℕ) {A : Set (Fin N → Ω)} (hA : MeasurableSet A) :
    (κ.real univ) ^ N ≤ (FinitePanelSampling.iidLaw μ N).real A +
      (1 - (FinitePanelSampling.iidLaw ν N).real A) := by
  have h := (abs_le.mp (iid_event_bound μ ν κ hκμ hκν N hA)).1
  linarith

lemma unit_interval_integrable (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2

theorem randomized_error_sum_lower_bound (μ ν κ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hκμ : κ ≤ μ) (hκν : κ ≤ ν)
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    κ.real univ ≤ (∫ x, f x ∂μ) + ∫ x, (1 - f x) ∂ν := by
  let : IsFiniteMeasure κ := ⟨(hκμ univ).trans_lt (measure_lt_top μ univ)⟩
  have hg : Measurable (fun x => 1 - f x) := measurable_const.sub hf
  have hgb : ∀ x, 0 ≤ 1 - f x ∧ 1 - f x ≤ 1 := by
    intro x
    constructor <;> linarith [(hb x).1, (hb x).2]
  have h1 := integral_mono_measure hκμ (ae_of_all _ fun x => (hb x).1)
    (unit_interval_integrable μ f hf hb)
  have h2 := integral_mono_measure hκν (ae_of_all _ fun x => (hgb x).1)
    (unit_interval_integrable ν (fun x => 1 - f x) hg hgb)
  have hk : (∫ x, f x ∂κ) + (∫ x, (1 - f x) ∂κ) = κ.real univ := by
    rw [← integral_add (unit_interval_integrable κ f hf hb)
      (unit_interval_integrable κ (fun x => 1 - f x) hg hgb)]
    have he : (fun x => f x + (1 - f x)) = fun _ => (1 : ℝ) := by funext x; ring
    rw [he, integral_const]
    simp only [smul_eq_mul, mul_one]
  linarith

theorem iid_randomized_error_sum_lower_bound (μ ν κ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hκμ : κ ≤ μ) (hκν : κ ≤ ν)
    (N : ℕ) (f : (Fin N → Ω) → ℝ) (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (κ.real univ) ^ N ≤ (∫ x, f x ∂FinitePanelSampling.iidLaw μ N) +
      ∫ x, (1 - f x) ∂FinitePanelSampling.iidLaw ν N := by
  let : IsFiniteMeasure κ := ⟨(hκμ univ).trans_lt (measure_lt_top μ univ)⟩
  simpa only [iid_mass] using randomized_error_sum_lower_bound _ _ _
    (iidLaw_mono hκμ N) (iidLaw_mono hκν N) f hf hb

end CommonSubmeasure
end Rhone.Statistics.Identifiability
