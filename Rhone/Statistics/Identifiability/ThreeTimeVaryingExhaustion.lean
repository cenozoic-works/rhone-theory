/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSilentWindow
public import Rhone.Statistics.Identifiability.ContinuousExposureOnset
public import Rhone.Statistics.Identifiability.TimeVaryingPairFlow
public import Rhone.Statistics.Identifiability.TimeVaryingPairExitKernel

/-! # Exhaust the first-migration/next-coalescence support orders for continuous histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma coalescence_clock_diverges_of_initial_pair (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (integratedClock c) atTop atTop := by
  apply timeVaryingPairMass_proper_coalescence_diverges k c q
    (fun t => timeVaryingPairTransition k c q 0 t 0) hc hcn
    (fun t _ j => inhomogeneousTransition_hasDerivAt_right _
      (SimultaneousOnset.pairGenerator_continuous k c q hc hq) 0 t 0 j)
    (fun t ht i => timeVaryingPairTransition_nonneg k c q hc hq hqn le_rfl ht 0 i) _ hproper
  ext i
  fin_cases i <;> simp [timeVaryingPairTransition_self k c q hc hq]

theorem exists_active_positive_witness (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hdiv : Tendsto (integratedClock c) atTop atTop)
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    ∃ t : ℝ, 0 < t ∧ 0 < c t ∧ 0 < witness k c q t := by
  obtain ⟨a, ha, hqbefore, hqafter⟩ := ExposureOnset.exists_first_onset q hq hqn hA hQ
  have hcshift : Continuous (fun u => c (a + u)) := hc.comp (continuous_const.add continuous_id)
  have hnshift (u : ℝ) (hu : 0 ≤ u) : 0 ≤ c (a + u) := hcn _ (add_nonneg ha hu)
  obtain ⟨B, hB, hCB⟩ := ExposureOnset.shifted_exposure_of_divergence c hc hdiv a
  obtain ⟨T, hT, hcbefore, hcafter⟩ :=
    ExposureOnset.exists_first_onset (fun u => c (a + u)) hcshift hnshift hB hCB
  by_cases hTzero : T = 0
  · subst T
    obtain ⟨δ, hδ, hW⟩ := witness_positive_after_migration_onset k c q hc hq hcn hqn ha hqbefore
    obtain ⟨u, hu, huδ, hcu⟩ := ExposureOnset.exists_positive_interior
      (fun u => c (a + u)) hcshift hnshift hδ
      (by simpa only [zero_add] using hcafter δ hδ)
    exact ⟨a + u, add_pos_of_nonneg_of_pos ha hu, hcu, hW u hu huδ (hqafter u hu)⟩
  · have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
    have hclosed : EqOn (fun u => c (a + u)) (fun _ => 0) (Icc 0 T) := by
      have he : EqOn (fun u => c (a + u)) (fun _ => 0) (Ioo 0 T) := hcbefore
      simpa only [closure_Ioo (ne_of_lt hTp)] using he.closure hcshift continuous_const
    have hsilent (u : ℝ) (hu : u ∈ Icc a (a + T)) : c u = 0 := by
      have h := hclosed (show u - a ∈ Icc 0 T by constructor <;> linarith [hu.1, hu.2])
      simpa only [add_sub_cancel] using h
    have hw := witness_positive_after_silent_window k c q hc hq hqn ha hT hqbefore
      hsilent (hqafter T hTp)
    obtain ⟨δ, hδ, hW⟩ := witness_positive_right k c q hc hq hw
    obtain ⟨u, hu, huδ, hcu⟩ := ExposureOnset.exists_positive_interior
      (fun u => c (a + T + u)) (hc.comp (continuous_const.add continuous_id))
      (fun u hu => hcn _ (add_nonneg (add_nonneg ha hT) hu)) hδ
      (by simpa only [add_assoc] using hcafter δ hδ)
    exact ⟨a + T + u, add_pos_of_nonneg_of_pos (add_nonneg ha hT) hu, hcu, hW u hu huδ⟩

end Rhone.Statistics.Identifiability.ThreeTimeVarying
