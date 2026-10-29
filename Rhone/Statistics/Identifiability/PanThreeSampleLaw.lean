/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AEDensityMarginals
public import Rhone.Statistics.Identifiability.PanClockCDF

/-! # Three-sample panmictic ordered merger-time and duration laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
namespace PanThreeSample
set_option backward.isDefEq.respectTransparency false

def firstDensity (rate : ℝ → ℝ) (s : ℝ) : ℝ :=
  3 * rate s * Real.exp (-3 * integratedClock rate s)

def jointDensity (rate : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  firstDensity rate p.1 * conditionalPairDensity rate (integratedClock rate) p.1 p.2

def law (rate : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  triangularDensityLaw (jointDensity rate)

lemma jointDensity_exp (rate : ℝ → ℝ) (s t : ℝ) :
    jointDensity rate (s,t) =
      3 * rate s * rate t * Real.exp (-2 * integratedClock rate s - integratedClock rate t) := by
  unfold jointDensity firstDensity conditionalPairDensity
  rw [show 3 * rate s * Real.exp (-3 * integratedClock rate s) *
      (rate t * Real.exp (integratedClock rate s - integratedClock rate t)) =
      3 * rate s * rate t * (Real.exp (-3 * integratedClock rate s) *
      Real.exp (integratedClock rate s - integratedClock rate t)) by ring,
    ← Real.exp_add]
  congr 2
  ring

lemma density_aemeasurable (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) :
    AEMeasurable (jointDensity rate) (planeVolume.restrict upperWedge) := by
  have hm : AEMeasurable rate volume := hr.aestronglyMeasurable.aemeasurable
  have hc := integratedClock_continuous rate hr
  have h1 : AEMeasurable (fun p : ℝ × ℝ => rate p.1) (volume.prod volume) := hm.comp_fst
  have h2 : AEMeasurable (fun p : ℝ × ℝ => rate p.2) (volume.prod volume) := hm.comp_snd
  have he : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-2 * integratedClock rate p.1 - integratedClock rate p.2)) := by fun_prop
  have h : AEMeasurable (jointDensity rate) (volume.prod volume) := by
    have heq : jointDensity rate = fun p : ℝ × ℝ =>
      3 * rate p.1 * rate p.2 *
        Real.exp (-2 * integratedClock rate p.1 - integratedClock rate p.2) := by
      funext p
      exact jointDensity_exp rate p.1 p.2
    rw [heq]
    exact ((aemeasurable_const.mul h1).mul h2).mul he.measurable.aemeasurable
  exact h.restrict

lemma clock_eq_halfLine (rate : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    integratedClock rate t = integrablePanClock rate t :=
  (integrablePanClock_eq_integral rate ht).symm

lemma conditional_lintegral_one (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal
      (conditionalPairDensity rate (integratedClock rate) s t)) = 1 := by
  have htail' : Tendsto (integrablePanClock rate) atTop atTop := by
    apply htail.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact clock_eq_halfLine rate ht
  have he := integrable_conditionalPair_lintegral_one (hr.locallyIntegrableOn _)
    (ae_of_all _ fun t _ => hn t) htail' hs
  rw [← he]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [conditionalPairDensity, clock_eq_halfLine rate hs,
    clock_eq_halfLine rate (hs.trans ht.le)]

lemma first_marginal (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    (law rate).map Prod.fst = panPairLaw (fun t => 3 * rate t) := by
  rw [law, triangular_map_fst_ae _ (density_aemeasurable rate hr)]
  unfold panPairLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ firstDensity rate s :=
    mul_nonneg (mul_nonneg (by norm_num) (hn s)) (Real.exp_pos _).le
  simp_rw [jointDensity, ENNReal.ofReal_mul hs0]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    conditional_lintegral_one rate hr hn htail hs.le, mul_one]
  congr 1
  change firstDensity rate s = 3 * rate s * Real.exp (-integratedClock (fun t => 3 * rate t) s)
  rw [integratedClock_scale]
  simp [firstDensity, neg_mul]

lemma first_lintegral_one (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    (∫⁻ s in Ioi 0, ENNReal.ofReal (firstDensity rate s)) = 1 := by
  let F := fun s => Real.exp (-3 * integratedClock rate s)
  have hac (b : ℝ) (_ : 0 ≤ b) : AbsolutelyContinuousOnInterval F 0 b :=
    ac_exp ((integratedClock_ac_zero rate hr b).const_mul (-3))
  have hd : ∀ᵐ s, 0 ≤ s → HasDerivAt F (-firstDensity rate s) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr] with s hs _
    have hclock : HasDerivAt (integratedClock rate) (rate s) s := hs 0
    convert! (hclock.const_mul (-3)).exp using 1
    dsimp only [firstDensity]
    ring
  have hn' : ∀ᵐ s, 0 ≤ s → 0 ≤ firstDensity rate s :=
    ae_of_all _ fun s _ => mul_nonneg (mul_nonneg (by norm_num) (hn s)) (Real.exp_pos _).le
  have hm : AEMeasurable (firstDensity rate) (volume.restrict (Ioi 0)) :=
    ((aemeasurable_const.mul hr.aestronglyMeasurable.aemeasurable).mul
      ((Real.continuous_exp.comp (continuous_const.mul
        (integratedClock_continuous rate hr))).measurable.aemeasurable)).restrict
  have hlim : Tendsto F atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul, Function.comp_def] using tendsto_neg_atTop_atBot.comp
      (htail.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  have he := ac_flux_lintegral_Ioi hac hd hn' hm hlim
  simpa [F, integratedClock] using he

lemma isProbability (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    IsProbabilityMeasure (law rate) := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (first_marginal rate hr hn htail)
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h
  constructor
  rw [h, panPairLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have heq : (fun t => ENNReal.ofReal (3 * rate t * Real.exp (-∫ x in 0..t, 3 * rate x))) =
      fun t => ENNReal.ofReal (firstDensity rate t) := by
    funext t
    change ENNReal.ofReal (3 * rate t * Real.exp (-integratedClock (fun x => 3 * rate x) t)) = _
    rw [integratedClock_scale]
    simp [firstDensity, neg_mul]
  rw [heq]
  exact first_lintegral_one rate hr hn htail

lemma preRoot_integral (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    {t : ℝ} (_ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, 3 * rate s * Real.exp (-2 * integratedClock rate s)) =
      (3/2 : ℝ) * (1 - Real.exp (-2 * integratedClock rate t)) := by
  let F := fun s => -(3/2 : ℝ) * Real.exp (-2 * integratedClock rate s)
  have hac : AbsolutelyContinuousOnInterval F 0 t :=
    (ac_exp ((integratedClock_ac_zero rate hr t).const_mul (-2))).const_mul (-(3/2))
  have hd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt F
      (3 * rate s * Real.exp (-2 * integratedClock rate s)) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr] with s hs _
    have hclock : HasDerivAt (integratedClock rate) (rate s) s := hs 0
    convert! ((hclock.const_mul (-2)).exp).const_mul (-(3/2 : ℝ)) using 1
    ring
  rw [ac_integral_eq_sub_ae hac hd]
  simp [F, integratedClock]
  ring

lemma column_lintegral (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ s, 0 ≤ rate s) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ s in Ioo 0 t, ENNReal.ofReal (jointDensity rate (s,t))) =
      ENNReal.ofReal ((3/2 : ℝ) * rate t *
        (Real.exp (-integratedClock rate t) - Real.exp (-3 * integratedClock rate t))) := by
  have hexp (s : ℝ) : jointDensity rate (s,t) =
      (rate t * Real.exp (-integratedClock rate t)) *
        (3 * rate s * Real.exp (-2 * integratedClock rate s)) := by
    rw [jointDensity_exp]
    rw [show -2 * integratedClock rate s - integratedClock rate t =
      -integratedClock rate t + -2 * integratedClock rate s by ring, Real.exp_add]
    ring
  have hc : 0 ≤ rate t * Real.exp (-integratedClock rate t) :=
    mul_nonneg (hn t) (Real.exp_pos _).le
  simp_rw [hexp, ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, restrict_Ioo_eq_restrict_Ioc]
  have hi : IntervalIntegrable
      (fun s => 3 * rate s * Real.exp (-2 * integratedClock rate s)) volume 0 t :=
    ((locallyIntegrable_interval rate hr 0 t).const_mul 3).mul_continuousOn
      (Real.continuous_exp.comp
        (continuous_const.mul (integratedClock_continuous rate hr))).continuousOn
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ fun s => mul_nonneg (mul_nonneg (by norm_num) (hn s)) (Real.exp_pos _).le),
    ← intervalIntegral.integral_of_le ht, preRoot_integral rate hr ht,
    ← ENNReal.ofReal_mul hc]
  congr 1
  have he : Real.exp (-integratedClock rate t) * Real.exp (-2 * integratedClock rate t) =
      Real.exp (-3 * integratedClock rate t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (3/2 : ℝ) * rate t * (Real.exp (-integratedClock rate t) -
      Real.exp (-integratedClock rate t) * Real.exp (-2 * integratedClock rate t)) := by ring
    _ = _ := by rw [he]

def rootDensity (rate : ℝ → ℝ) (t : ℝ) : ℝ :=
  (3/2 : ℝ) * rate t *
    (Real.exp (-integratedClock rate t) - Real.exp (-3 * integratedClock rate t))

lemma root_marginal (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) :
    (law rate).map Prod.snd = (volume.restrict (Ioi 0)).withDensity
      (fun t => ENNReal.ofReal (rootDensity rate t)) := by
  rw [law, triangular_map_snd_positive_ae _ (density_aemeasurable rate hr)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact column_lintegral rate hr hn ht.le

lemma rootDensity_nonneg (rate : ℝ → ℝ) (hn : ∀ t, 0 ≤ rate t)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ rootDensity rate t := by
  have hH : 0 ≤ integratedClock rate t := by
    rw [clock_eq_halfLine rate ht]
    exact integrablePanClock_nonneg (ae_of_all _ fun t _ => hn t) ht
  exact mul_nonneg (mul_nonneg (by norm_num) (hn t))
    (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))

lemma root_cdf (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) {t : ℝ} (ht : 0 ≤ t) :
    ((law rate).map Prod.snd).real (Ioc 0 t) =
      1 - ((3/2 : ℝ) * Real.exp (-integratedClock rate t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate t)) := by
  let F := fun s => 1 - ((3/2 : ℝ) * Real.exp (-integratedClock rate s) -
    (1/2 : ℝ) * Real.exp (-3 * integratedClock rate s))
  have hac : AbsolutelyContinuousOnInterval F 0 t :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub
      (((ac_exp (integratedClock_ac_zero rate hr t).neg).const_mul (3/2)).sub
        ((ac_exp ((integratedClock_ac_zero rate hr t).const_mul (-3))).const_mul (1/2)))
  have hd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt F (rootDensity rate s) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr] with s hs _
    have hclock : HasDerivAt (integratedClock rate) (rate s) s := hs 0
    convert! (((hclock.neg.exp).const_mul (3/2 : ℝ)).sub
      (((hclock.const_mul (-3)).exp).const_mul (1/2 : ℝ))).const_sub 1 using 1
    dsimp only [rootDensity, Pi.neg_apply]
    ring
  rw [root_marginal rate hr hn, positive_density_real_Ioc _ ht
    (ac_intervalIntegrable_ae hac hd)]
  · rw [ac_integral_eq_sub_ae hac hd]
    norm_num [F, integratedClock]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact rootDensity_nonneg rate hn hs.1.le

lemma root_survival (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) {t : ℝ} (ht : 0 ≤ t) :
    1 - ((law rate).map Prod.snd).real (Ioc 0 t) =
      (3/2 : ℝ) * Real.exp (-integratedClock rate t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate t) := by
  rw [root_cdf rate hr hn ht]
  ring

lemma first_survival (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    1 - ((law rate).map Prod.fst).real (Ioc 0 t) =
      Real.exp (-3 * integratedClock rate t) := by
  rw [first_marginal rate hr hn htail, panPairLaw_real_Ioc _
    (by convert! hr.smul (3 : ℝ) using 1) (fun s => mul_nonneg (by norm_num) (hn s)) ht,
    integratedClock_scale]
  simp [neg_mul]

lemma random_pair_survival (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    (1/3 : ℝ) * (1 - ((law rate).map Prod.fst).real (Ioc 0 t)) +
      (2/3 : ℝ) * (1 - ((law rate).map Prod.snd).real (Ioc 0 t)) =
      1 - (panPairLaw rate).real (Ioc 0 t) := by
  rw [first_survival rate hr hn htail ht, root_survival rate hr hn ht,
    panPairLaw_real_Ioc rate hr hn ht]
  ring

def toDurations (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 - p.1)

def toOrdered (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.1 + p.2)

lemma measurable_toDurations : Measurable toDurations := by unfold toDurations; fun_prop
lemma measurable_toOrdered : Measurable toOrdered := by unfold toOrdered; fun_prop

lemma toOrdered_toDurations (p : ℝ × ℝ) : toOrdered (toDurations p) = p := by
  apply Prod.ext
  · rfl
  · dsimp [toOrdered, toDurations]
    ring

def durationLaw (rate : ℝ → ℝ) : Measure (ℝ × ℝ) := (law rate).map toDurations

lemma durationLaw_probability (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    IsProbabilityMeasure (durationLaw rate) := by
  have := isProbability rate hr hn htail
  unfold durationLaw
  infer_instance

lemma law_ordered_support (rate : ℝ → ℝ) :
    ∀ᵐ p ∂law rate, 0 < p.1 ∧ p.1 < p.2 := by
  have h : ∀ᵐ p ∂planeVolume.restrict upperWedge, p ∈ upperWedge :=
    ae_restrict_mem upperWedge_open.measurableSet
  exact (withDensity_absolutelyContinuous _ _).ae_le h

lemma durationLaw_nonnegative (rate : ℝ → ℝ) :
    ∀ᵐ p ∂durationLaw rate, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  apply (ae_map_iff measurable_toDurations.aemeasurable
    (show MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [law_ordered_support rate] with p hp
  exact ⟨hp.1.le, sub_nonneg.mpr hp.2.le⟩

lemma recover_ordered_law (rate : ℝ → ℝ) :
    (durationLaw rate).map toOrdered = law rate := by
  rw [durationLaw, Measure.map_map measurable_toOrdered measurable_toDurations]
  have h : toOrdered ∘ toDurations = id := funext toOrdered_toDurations
  rw [h, Measure.map_id]

lemma durationLaw_first_marginal (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    (durationLaw rate).map Prod.fst = panPairLaw (fun t => 3 * rate t) := by
  rw [durationLaw, Measure.map_map measurable_fst measurable_toDurations]
  exact first_marginal rate hr hn htail

lemma durationLaw_root_cdf (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) {t : ℝ} (ht : 0 ≤ t) :
    ((durationLaw rate).map (fun p => p.1 + p.2)).real (Ioc 0 t) =
      1 - ((3/2 : ℝ) * Real.exp (-integratedClock rate t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate t)) := by
  rw [durationLaw, Measure.map_map (by fun_prop) measurable_toDurations]
  have h : (fun p : ℝ × ℝ => p.1 + p.2) ∘ toDurations = Prod.snd := by
    funext p
    dsimp [toDurations]
    ring
  rw [h]
  exact root_cdf rate hr hn ht

end PanThreeSample
end Rhone.Statistics.Identifiability
