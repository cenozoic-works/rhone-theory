/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanExistence
public import Rhone.Statistics.Identifiability.ClockLawMarginal
public import Rhone.Statistics.Identifiability.RegularJointLawNormalization

/-! # Absolutely continuous clock calculus: integrals, half-line extensions, continuity -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem ac_integral_eq_sub_ae {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hd] with x hx hxmem
  exact (hx (uIoc_subset_uIcc hxmem)).deriv.symm

theorem ac_intervalIntegrable_ae {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    IntervalIntegrable g volume a b := by
  apply hf.intervalIntegrable_deriv.congr_ae
  change ∀ᵐ x ∂volume.restrict (uIoc a b), deriv f x = g x
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hd] with x hx hxmem
  exact (hx (uIoc_subset_uIcc hxmem)).deriv

theorem ac_flux_lintegral_Ioi {F g : ℝ → ℝ} {a c : ℝ}
    (hac : ∀ b, a ≤ b → AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ x, a ≤ x → HasDerivAt F (-g x) x)
    (hn : ∀ᵐ x, a ≤ x → 0 ≤ g x)
    (hm : AEMeasurable g (volume.restrict (Ioi a)))
    (htail : Tendsto F atTop (𝓝 c)) :
    (∫⁻ x in Ioi a, ENNReal.ofReal (g x)) = ENNReal.ofReal (F a - c) := by
  have hcompact (b : ℝ) (hb : a ≤ b) :
      (∫⁻ x in Ioc a b, ENNReal.ofReal (g x)) = ENNReal.ofReal (F a - F b) := by
    have hd' : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun y => -F y) (g x) x := by
      filter_upwards [hd] with x hx hmem
      have hx0 : a ≤ x := (by simpa only [uIcc_of_le hb] using hmem : x ∈ Icc a b).1
      convert! (hx hx0).neg using 1
      simp only [neg_neg]
    have hi := ac_intervalIntegrable_ae (hac b hb).neg hd'
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1]
    · rw [← intervalIntegral.integral_of_le hb, ac_integral_eq_sub_ae (hac b hb).neg hd']
      congr 1
      change -F b - -F a = _
      ring
    · change ∀ᵐ x ∂volume.restrict (Ioc a b), 0 ≤ g x
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hn] with x hx hmem
      exact hx hmem.1.le
  apply (aecover_Iic (μ := volume.restrict (Ioi a)) tendsto_id).lintegral_eq_of_tendsto
    (ENNReal.ofReal (F a - c)) hm.ennreal_ofReal
  have ht := (ENNReal.continuous_ofReal.tendsto (F a - c)).comp
    (tendsto_const_nhds.sub htail)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [Measure.restrict_restrict measurableSet_Iic, inter_comm]
  exact (hcompact b hb).symm

theorem halfLineAC_continuousOn {f : ℝ → ℝ}
    (hf : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) :
    ContinuousOn f (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hac := (hf (t + 1) (by linarith : 0 ≤ t + 1)).continuousOn
  rw [uIcc_of_le (by linarith : 0 ≤ t + 1)] at hac
  apply (hac t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
  have hn : Iio (t + 1) ∈ 𝓝 t := Iio_mem_nhds (by linarith)
  filter_upwards [mem_of_superset (inter_mem_nhdsWithin (Ici (0 : ℝ)) hn) (fun x hx =>
    (show x ∈ Icc 0 (t+1) from ⟨hx.1, hx.2.le⟩))] with x hx using hx

theorem halfLineAC_zeroExtension_aemeasurable {f : ℝ → ℝ}
    (hf : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) :
    AEMeasurable (panZeroExtension f) volume := by
  have hm : AEStronglyMeasurable f (volume.restrict (Ici 0)) :=
    (halfLineAC_continuousOn hf).aestronglyMeasurable measurableSet_Ici
  exact ((aestronglyMeasurable_indicator_iff measurableSet_Ici).mpr hm).aemeasurable

theorem integrablePanClock_continuous {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume) : Continuous (integrablePanClock rate) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hc := (integrablePanClock_ac hr (t-1) (t+1)).continuousOn
  rw [uIcc_of_le (by linarith : t-1 ≤ t+1)] at hc
  exact (hc t ⟨by linarith, by linarith⟩).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

theorem integrable_conditionalPair_lintegral_one {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal
      (conditionalPairDensity rate (integrablePanClock rate) s t)) = 1 := by
  let H := integrablePanClock rate
  let F := fun t => Real.exp (H s - H t)
  let g := conditionalPairDensity rate H s
  have hac (b : ℝ) (_hb : s ≤ b) : AbsolutelyContinuousOnInterval F s b :=
    ac_exp (((LipschitzWith.const (H s)).lipschitzOnWith.absolutelyContinuousOnInterval).sub
      (integrablePanClock_ac hr s b))
  have hd : ∀ᵐ t, s ≤ t → HasDerivAt F (-g t) t := by
    filter_upwards [integrablePanClock_ae_hasDerivAt hr] with t ht hst
    convert ((ht (hs.trans hst)).const_sub (H s)).exp using 1
    dsimp [g, conditionalPairDensity]
    ring
  have hn : ∀ᵐ t, s ≤ t → 0 ≤ g t := by
    filter_upwards [hrn] with t ht hst
    exact mul_nonneg (ht (hs.trans hst)) (Real.exp_pos _).le
  have hm : AEMeasurable g (volume.restrict (Ioi s)) :=
    ((hr.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono (fun t ht => hs.trans ht.le) le_rfl))).mul
      ((Real.continuous_exp.comp (continuous_const.sub
        (integrablePanClock_continuous hr))).measurable.aemeasurable)
  have hlim : Tendsto F atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [sub_eq_add_neg, H, Function.comp_apply] using tendsto_atBot_add_const_left atTop
      (H s)
      (tendsto_neg_atTop_atBot.comp htail)
  have he := ac_flux_lintegral_Ioi hac hd hn hm hlim
  simpa [F] using he

end Rhone.Statistics.Identifiability
