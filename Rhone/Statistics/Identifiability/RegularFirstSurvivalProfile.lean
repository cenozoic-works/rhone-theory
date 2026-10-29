/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ScalarACClockIdentity
public import Rhone.Statistics.Identifiability.ThreeSampleCDFStatistic

/-! # An observable first-merger survival profile constructs its unique candidate pan clock -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership

structure FirstSurvivalProfile where
  survival : ℝ → ℝ
  density : ℝ → ℝ
  continuous_survival : Continuous survival
  initial : survival 0 = 1
  positive : ∀ t, 0 ≤ t → 0 < survival t
  ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval survival 0 T
  density_locallyIntegrable : LocallyIntegrableOn density (Ici 0) volume
  density_nonnegative : ∀ᵐ t, 0 ≤ t → 0 ≤ density t
  derivative_ae : ∀ᵐ t, 0 ≤ t → HasDerivAt survival (-density t) t
  proper : Tendsto survival atTop (𝓝 0)

namespace FirstSurvivalProfile

def rawRate (P : FirstSurvivalProfile) (t : ℝ) : ℝ :=
  panZeroExtension P.density t / (3 * P.survival (max t 0))

def rate (P : FirstSurvivalProfile) : ℝ → ℝ :=
  PanThreeSample.nonnegativeRepresentative P.rawRate

lemma rawRate_locallyIntegrable (P : FirstSurvivalProfile) :
    LocallyIntegrable P.rawRate volume := by
  have hrec : Continuous (fun t : ℝ => 1 / (3 * P.survival (max t 0))) :=
    continuous_const.div
      (continuous_const.mul (P.continuous_survival.comp (continuous_id.max continuous_const)))
      (fun t => mul_ne_zero (by norm_num) (P.positive _ (le_max_right t 0)).ne')
  have h := (panZeroExtension_locallyIntegrable P.density_locallyIntegrable).mul_continuous hrec
  unfold rawRate
  simpa only [div_eq_mul_inv, one_mul] using h

lemma rawRate_nonnegative_ae (P : FirstSurvivalProfile) :
    ∀ᵐ t, 0 ≤ t → 0 ≤ P.rawRate t := by
  filter_upwards [P.density_nonnegative] with t ht ht0
  unfold rawRate
  rw [panZeroExtension_of_nonneg P.density ht0, max_eq_left ht0]
  exact div_nonneg (ht ht0) (mul_nonneg (by norm_num) (P.positive t ht0).le)

lemma rate_locallyIntegrable (P : FirstSurvivalProfile) : LocallyIntegrable P.rate volume :=
  PanThreeSample.representative_locallyIntegrable
    (P.rawRate_locallyIntegrable.locallyIntegrableOn _)

lemma rate_nonnegative (P : FirstSurvivalProfile) (t : ℝ) : 0 ≤ P.rate t :=
  PanThreeSample.representative_nonneg P.rawRate t

lemma rate_eq_ae (P : FirstSurvivalProfile) :
    ∀ᵐ t, 0 ≤ t → P.rate t = P.density t / (3 * P.survival t) := by
  filter_upwards [PanThreeSample.representative_eq_ae P.rawRate_nonnegative_ae] with t ht ht0
  change PanThreeSample.nonnegativeRepresentative P.rawRate t = _
  rw [← ht ht0]
  simp only [rawRate, panZeroExtension_of_nonneg P.density ht0, max_eq_left ht0]

lemma survival_eq_clock (P : FirstSurvivalProfile) {T : ℝ} (hT : 0 ≤ T) :
    P.survival T = Real.exp (-3 * integratedClock P.rate T) := by
  have h3 : LocallyIntegrable (fun t => 3 * P.rate t) volume := by
    convert! P.rate_locallyIntegrable.smul (3 : ℝ) using 1
  have hd : ∀ᵐ t, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt P.survival (-(3 * P.rate t) * P.survival t) t := by
    filter_upwards [P.derivative_ae, P.rate_eq_ae] with t ht hrt hmem
    have ht0 : 0 ≤ t := (uIcc_of_le hT ▸ hmem).1
    apply (ht ht0).congr_deriv
    rw [hrt ht0]
    field_simp [(P.positive t ht0).ne']
  have he := scalar_ac_survival_identity (fun t => 3 * P.rate t) P.survival h3
    0 T (P.ac T hT) hd
  simpa [integratedClock, intervalIntegral.integral_const_mul, P.initial] using he

lemma clock_diverges (P : FirstSurvivalProfile) :
    Tendsto (integratedClock P.rate) atTop atTop := by
  have h3 : Tendsto (fun t => 3 * integratedClock P.rate t) atTop atTop := by
    apply tendsto_atTop_of_survival_lower_bound P.survival
      (fun t => 3 * integratedClock P.rate t) (a := 1) (by norm_num) P.proper
    intro t ht
    simpa only [one_mul, neg_mul] using (P.survival_eq_clock ht).ge
  have h := h3.const_mul_atTop (show (0 : ℝ) < 1 / 3 by norm_num)
  simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (3 : ℝ) ≠ 0), one_mul] using h

end FirstSurvivalProfile
end Rhone.Statistics.Identifiability.ThreeSampleMembership
