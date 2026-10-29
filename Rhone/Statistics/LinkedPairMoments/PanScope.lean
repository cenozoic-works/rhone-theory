/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Power
public import Rhone.Statistics.GeneralPairTimePower.PooledWitness

/-! # Pan-comparator scope, with an explicit hazard realizability premise -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.LinkedPairMoments
open PairObservationChannel DependenceBudget GeneralPairTimePower
open MarkovChain.Identifiability Identifiability
variable {K : ℕ} {H : Type*} [Fintype H]

def panPanelLaw (E : Channel K H) (r : ℝ → ℝ) (hr : AdmittedPan r)
    {κ : ℝ} (hκ : 0 ≤ κ) (L : ℕ) : Law (Fin L → H × H) := by
  letI := PanThreeSample.pairLaw_probability r hr.1 hr.2.1 hr.2.2
  exact panelLaw E (panPairLaw r) hκ
    ((PanThreeSample.pairLaw_positive_support r).mono fun _ h => h.le) L

theorem exists_uniform_pan_separator (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (hne : μ ≠ ν) :
    ∃ L : ℕ, ∀ r : ℝ → ℝ, ∀ hr : AdmittedPan r, ∀ κ : ℝ, ∀ hκ : 0 ≤ κ,
      ¬(panelLaw E μ hk.le hμ L = panPanelLaw E r hr hκ L ∧
        panelLaw E ν hk.le hν L = panPanelLaw E r hr hκ L) := by
  obtain ⟨L, hL⟩ := (some_panel_separates_iff E hE μ ν hk hμ hν).mpr hne
  exact ⟨L, fun _ _ _ _ he => hL (he.1.trans he.2.symm)⟩

theorem all_panels_pan_match_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (hreal : ∃ r : ℝ → ℝ, AdmittedPan r ∧ μ = panPairLaw r) :
    (∃ r : ℝ → ℝ, ∃ hr : AdmittedPan r, ∃ κ : ℝ, ∃ hκ : 0 ≤ κ, ∀ L : ℕ,
      panelLaw E μ hk.le hμ L = panPanelLaw E r hr hκ L ∧
      panelLaw E ν hk.le hν L = panPanelLaw E r hr hκ L) ↔ μ = ν := by
  constructor
  · rintro ⟨r, hr, κ, hκ, he⟩
    exact (all_panels_eq_iff E hE μ ν hk hμ hν).mp
      (fun L => (he L).1.trans (he L).2.symm)
  · intro he
    subst ν
    obtain ⟨r, hr, hreal⟩ := hreal
    refine ⟨r, hr, k, hk.le, fun L => ?_⟩
    have hh : panelLaw E μ hk.le hμ L = panPanelLaw E r hr hk.le L := by
      apply finite_law_ext
      intro x
      change (∫ t, panelWeight E k t L x ∂μ) =
        ∫ t, panelWeight E k t L x ∂panPairLaw r
      rw [hreal]
    exact ⟨hh, hh⟩

end Rhone.Statistics.LinkedPairMoments
