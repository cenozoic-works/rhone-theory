/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingMassBounds

/-!
# Proper observed finite-time mass recovers the first marginal without conditional-tail assumptions
-/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeSampling

lemma law_first_marginal_le (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    (law ρ k c q).map Prod.fst ≤ firstLaw ρ k c q := by
  rw [law, triangular_map_fst_ae _ (jointDensity_aemeasurable ρ k c q hc hq)]
  apply withDensity_mono
  filter_upwards [hcn.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with s hcs hs
  exact jointDensity_row_lintegral_le ρ k c q hρ hc hq hcn hqn hs (hcs hs.le)

lemma law_mass_le_one (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    law ρ k c q univ ≤ 1 := by
  have h := (law_first_marginal_le ρ k c q hρ hc hq hcn hqn) univ
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h
  exact h.trans (firstLaw_mass_le_one ρ k c q hρ hρsum hc hq hcn hqn)

lemma law_isFinite (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    IsFiniteMeasure (law ρ k c q) :=
  ⟨(law_mass_le_one ρ k c q hρ hρsum hc hq hcn hqn).trans_lt (by simp)⟩

lemma law_first_marginal_of_probability (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    [IsProbabilityMeasure (law ρ k c q)]
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    (law ρ k c q).map Prod.fst = firstLaw ρ k c q := by
  let : IsProbabilityMeasure ((law ρ k c q).map Prod.fst) :=
    inferInstance
  have hle := law_first_marginal_le ρ k c q hρ hc hq hcn hqn
  apply Measure.eq_of_le_of_measure_univ_eq hle
  apply le_antisymm (hle univ)
  simpa only [measure_univ] using firstLaw_mass_le_one ρ k c q hρ hρsum hc hq hcn hqn

end Rhone.Statistics.Identifiability.ThreeSampling
