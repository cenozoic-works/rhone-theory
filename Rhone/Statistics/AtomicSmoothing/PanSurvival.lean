/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.ClippedClock

/-! # A proper locally integrable pan rate from the concrete mixture CDF -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Rhone.Statistics.AtomicSmoothing
open Algebra.Identifiability MarkovChain.Identifiability Identifiability ThreeSampleMembership

variable {α : Type*} [Fintype α]

lemma clip_monotone : Monotone clip := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

lemma componentCDF_monotone (a : ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1) :
    Monotone (componentCDF a τ) := by
  intro x y hxy
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr h1)
    apply clip_monotone
    exact div_le_div_of_nonneg_right (sub_le_sub_right hxy _) (by positivity)
  · exact mul_le_mul_of_nonneg_left (clip_monotone hxy) hτ.le

lemma mixtureCDF_monotone (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1)
    (hw : ∀ a, 0 ≤ w a) : Monotone (mixtureCDF loc w τ) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (componentCDF_monotone (loc a) hτ h1 hxy) (hw a)

def survival (loc w : α → ℝ) (τ t : ℝ) : ℝ := mixtureCDF loc w τ (unitClock t)

lemma survival_lipschitz (loc w : α → ℝ) (τ : ℝ) :
    ∃ K, LipschitzWith K (survival loc w τ) := by
  obtain ⟨K, hK⟩ := mixtureCDF_lipschitz loc w τ
  exact ⟨K * 1, hK.comp unitClock_lipschitz⟩

lemma survival_antitone (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1)
    (hw : ∀ a, 0 ≤ w a) : Antitone (survival loc w τ) := by
  intro s t hst
  exact mixtureCDF_monotone loc w hτ h1 hw (unitClock_antitone hst)

lemma survival_positive (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (t : ℝ) : 0 < survival loc w τ t := by
  have hl := mixtureCDF_lower loc w h1 hw hs (unitClock_positive t).le (unitClock_le_one t)
  exact (mul_pos hτ (unitClock_positive t)).trans_le hl

lemma survival_zero (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ a, loc a + τ ≤ 1) (hs : ∑ a, w a = 1) : survival loc w τ 0 = 1 := by
  rw [survival, unitClock_zero, mixtureCDF_one loc w hτ hu hs]

lemma survival_proper (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hl : ∀ a, 0 ≤ loc a - τ) : Tendsto (survival loc w τ) atTop (𝓝 (0 : ℝ)) := by
  have hc : ContinuousAt (mixtureCDF loc w τ) 0 := (mixtureCDF_continuous loc w τ).continuousAt
  have he := hc.tendsto.comp unitClock_tendsto
  rw [mixtureCDF_zero loc w hτ hl] at he
  exact he

def regularSurvival (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hl : ∀ a, 0 ≤ loc a - τ) (hu : ∀ a, loc a + τ ≤ 1) : RegularPairSurvival where
  u := survival loc w τ
  d := deriv (survival loc w τ)
  continuous_u := (survival_lipschitz loc w τ).choose_spec.continuous
  locallyIntegrable_d := lipschitz_deriv_locallyIntegrable (survival_lipschitz loc w τ).choose_spec
  ac := fun _ _ => (survival_lipschitz loc w τ).choose_spec.lipschitzOnWith
    |>.absolutelyContinuousOnInterval
  derivative_ae := ((survival_lipschitz loc w τ).choose_spec.ae_differentiableAt_real).mono
    (fun _ ht _ => ht.hasDerivAt)
  initial := survival_zero loc w hτ hu hs
  positive := fun t _ => survival_positive loc w hτ h1 hw hs t
  decreasing_ae := ae_of_all _ fun _ _ => (survival_antitone loc w hτ h1 hw).deriv_nonpos
  proper := survival_proper loc w hτ hl

theorem exists_regular_pan_rate (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hl : ∀ a, 0 ≤ loc a - τ) (hu : ∀ a, loc a + τ ≤ 1) :
    ∃ r : ℝ → ℝ, LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧
      Tendsto (integratedClock r) atTop atTop ∧
      ∀ t : ℝ, 0 ≤ t → Real.exp (-integratedClock r t) = mixtureCDF loc w τ (Real.exp (-t)) := by
  let P := regularSurvival loc w hτ h1 hw hs hl hu
  refine ⟨P.firstProfile.rate, P.firstProfile.rate_locallyIntegrable,
    P.firstProfile.rate_nonnegative, P.firstProfile.clock_diverges, ?_⟩
  intro t ht
  rw [← P.survival_eq_clock ht]
  change survival loc w τ t = _
  rw [survival, unitClock_eq ht]

end Rhone.Statistics.AtomicSmoothing
