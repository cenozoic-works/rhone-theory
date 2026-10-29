/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DensityMarginals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The sum pushforward of a regular symmetric joint law -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

noncomputable def panSumDensity (δ a f : ℝ → ℝ) (z : ℝ) : ℝ :=
  δ (z / 2) / 2 + 2 * ∫ s in 0..z / 2, a s * f (z - s)

theorem triangularDensityLaw_map_sum (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map (fun p => p.1 + p.2) =
      volume.withDensity (fun z => ∫⁻ s in Ioo 0 (z / 2),
        ENNReal.ofReal (j (s, z - s))) := by
  have he : (fun p : ℝ × ℝ => p.1 + p.2) = Prod.snd ∘ upperShear := rfl
  rw [he, ← Measure.map_map measurable_snd upperShear.measurable,
    triangularDensityLaw, ← withDensity_indicator upperWedge_open.measurableSet,
    equiv_map_withDensity _ upperShear _
      (hj.ennreal_ofReal.indicator upperWedge_open.measurableSet),
    upperShear_preserving.map_eq]
  change ((volume.prod volume).withDensity
    ((upperWedge.indicator (fun p => ENNReal.ofReal (j p))) ∘ upperShear.symm)).map Prod.snd = _
  rw [product_density_map_snd
    ((hj.ennreal_ofReal.indicator upperWedge_open.measurableSet).comp
      upperShear.symm.measurable)]
  congr 1
  funext z
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro s
  have heq : upperShear.symm (s,z) = (s, z - s) := by
    simp only [upperShear_symm_apply]
    congr 1
    ring
  simp only [Function.comp_apply]
  rw [heq]
  have hm : (s, z - s) ∈ upperWedge ↔ s ∈ Ioo 0 (z / 2) := by
    change (0 < s ∧ s < z-s) ↔ (0 < s ∧ s < z/2)
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  by_cases hs : s ∈ Ioo 0 (z / 2)
  · simp only [indicator_of_mem hs, indicator_of_mem (hm.mpr hs)]
  · simp only [indicator_of_notMem hs, indicator_of_notMem (mt hm.mp hs)]

theorem positive_volume_map_double :
    (volume.restrict (Ioi (0 : ℝ))).map (fun t => 2*t) =
      ENNReal.ofReal (1/2 : ℝ) • volume.restrict (Ioi (0 : ℝ)) := by
  have he : (fun t : ℝ => 2*t) ⁻¹' Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  conv_lhs => rw [← he]
  rw [← Measure.restrict_map (f := fun t : ℝ => 2*t)
    (measurable_const.mul measurable_id) measurableSet_Ioi,
    Real.map_volume_mul_left (by norm_num : (2:ℝ) ≠ 0), Measure.restrict_smul]
  norm_num

theorem diagonalDensityLaw_map_sum (δ : ℝ → ℝ) (hδ : Measurable δ) :
    (diagonalDensityLaw δ).map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun z => ENNReal.ofReal (δ (z / 2) / 2)) := by
  rw [diagonalDensityLaw, Measure.map_map
    (f := fun t : ℝ => (t,t)) (g := fun p : ℝ × ℝ => p.1 + p.2)
    (measurable_fst.add measurable_snd) (measurable_id.prodMk measurable_id)]
  have hd : ((fun p : ℝ × ℝ => p.1 + p.2) ∘ fun t : ℝ => (t,t)) =
      MeasurableEquiv.mulLeft₀ (2:ℝ) (by norm_num) := by
    funext t
    change t+t = 2*t
    ring
  rw [hd, equiv_map_withDensity _ _ _ hδ.ennreal_ofReal]
  simp only [MeasurableEquiv.symm_mulLeft₀, MeasurableEquiv.coe_mulLeft₀]
  rw [positive_volume_map_double, withDensity_smul_measure,
    ← withDensity_smul' _ _ (by simp)]
  congr 1
  funext z
  change ENNReal.ofReal (1/2:ℝ) * ENNReal.ofReal (δ (2⁻¹*z)) = _
  rw [← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [show (2:ℝ)⁻¹*z = z/2 by ring]
  ring

theorem measurable_triangular_sum_density (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    Measurable (fun z : ℝ => ∫⁻ s in Ioo 0 (z / 2), ENNReal.ofReal (j (s, z - s))) := by
  let W : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2/2}
  have hW : MeasurableSet W :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst (measurable_snd.div_const 2))
  have hm : Measurable (W.indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal (j (p.1,p.2-p.1)))) :=
    (hj.comp (measurable_fst.prodMk (measurable_snd.sub
      measurable_fst))).ennreal_ofReal.indicator hW
  have he : (fun z : ℝ => ∫⁻ s in Ioo 0 (z / 2), ENNReal.ofReal (j (s, z - s))) =
      (fun z => ∫⁻ s, W.indicator (fun p => ENNReal.ofReal (j (p.1,p.2-p.1))) (s,z)) := by
    funext z
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro s
    have hsw : (s,z) ∈ W ↔ s ∈ Ioo 0 (z / 2) := Iff.rfl
    by_cases hs : s ∈ Ioo 0 (z / 2)
    · rw [indicator_of_mem hs, indicator_of_mem (hsw.mpr hs)]
    · rw [indicator_of_notMem hs, indicator_of_notMem (mt hsw.mp hs)]
  rw [he]
  exact hm.lintegral_prod_left'

theorem triangularDensityLaw_map_sum_positive (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z =>
        ∫⁻ s in Ioo 0 (z / 2), ENNReal.ofReal (j (s, z - s))) := by
  rw [triangularDensityLaw_map_sum j hj, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext z
  by_cases hz : 0 < z
  · rw [indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz)]
  · rw [indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz), Ioo_eq_empty (by linarith : ¬ 0 < z/2)]
    simp

theorem regularJointLaw_map_sum (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ)
    (hδ : Measurable δ) (hj : Measurable j) :
    (regularJointLaw δ j).map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z =>
        ENNReal.ofReal (δ (z / 2)/2) +
          2 * ∫⁻ s in Ioo 0 (z / 2), ENNReal.ofReal (j (s, z - s))) := by
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hs : ((triangularDensityLaw j).map Prod.swap).map (fun p => p.1 + p.2) =
      (triangularDensityLaw j).map (fun p => p.1 + p.2) := by
    rw [Measure.map_map (f := Prod.swap) (g := fun p : ℝ × ℝ => p.1 + p.2)
      hm measurable_swap]
    congr 1
    funext p
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  rw [regularJointLaw, Measure.map_add _ _ hm, Measure.map_add _ _ hm, hs,
    diagonalDensityLaw_map_sum δ hδ, triangularDensityLaw_map_sum_positive j hj]
  have hd : Measurable (fun z : ℝ => ENNReal.ofReal (δ (z / 2)/2)) :=
    ((hδ.comp (measurable_id.div_const 2)).div_const 2).ennreal_ofReal
  have ht := measurable_triangular_sum_density j hj
  rw [← withDensity_add_left hd, ← withDensity_add_left (hd.add ht)]
  congr 1
  funext z
  simp only [Pi.add_apply, two_mul]
  ac_rfl

theorem triangular_sum_lintegral_eq_ofReal (j : ℝ × ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hi : IntervalIntegrable (fun s => j (s, z - s)) volume 0 (z / 2))
    (hn : ∀ p ∈ upperWedge, 0 ≤ j p) :
    (∫⁻ s in Ioo 0 (z / 2), ENNReal.ofReal (j (s, z - s))) =
      ENNReal.ofReal (∫ s in 0..z/2, j (s, z - s)) := by
  rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ z/2), integral_Ioc_eq_integral_Ioo]
  apply (ofReal_integral_eq_lintegral_ofReal (hi.1.mono_set Ioo_subset_Ioc_self) _).symm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  apply hn (s, z - s)
  change 0 < s ∧ s < z-s
  constructor <;> linarith [hs.1,hs.2]

theorem regularJointLaw_map_sum_real (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ)
    (hδ : Measurable δ) (hj : Measurable j)
    (hδn : ∀ t > 0, 0 ≤ δ t) (hjn : ∀ p ∈ upperWedge, 0 ≤ j p)
    (hji : ∀ z > 0, IntervalIntegrable (fun s => j (s, z - s)) volume 0 (z / 2)) :
    (regularJointLaw δ j).map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z =>
        ENNReal.ofReal (δ (z / 2)/2 + 2 * ∫ s in 0..z/2, j (s, z - s))) := by
  rw [regularJointLaw_map_sum δ j hδ hj]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz' : 0 < z := hz
  have hi : 0 ≤ ∫ s in 0..z/2, j (s, z - s) := by
    rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ z/2), integral_Ioc_eq_integral_Ioo]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply hjn (s, z - s)
    change 0 < s ∧ s < z-s
    constructor <;> linarith [hs.1,hs.2]
  rw [triangular_sum_lintegral_eq_ofReal j hz' (hji z hz') hjn,
    ENNReal.ofReal_add (div_nonneg (hδn _ (by linarith)) (by norm_num))
      (mul_nonneg (by norm_num) hi), ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem regularJointLaw_map_sum_pan (δ a f : ℝ → ℝ)
    (hδ : Measurable δ) (ha : Continuous a) (hf : Continuous f)
    (hδn : ∀ t > 0, 0 ≤ δ t) (han : ∀ t > 0, 0 ≤ a t)
    (hfn : ∀ t > 0, 0 ≤ f t) :
    (regularJointLaw δ (fun p => a p.1 * f p.2)).map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z => ENNReal.ofReal (panSumDensity δ a
        f z)) := by
  apply regularJointLaw_map_sum_real δ (fun p => a p.1 * f p.2) hδ
    ((ha.measurable.comp measurable_fst).mul (hf.measurable.comp measurable_snd)) hδn
  · intro p hp
    exact mul_nonneg (han _ hp.1) (hfn _ (lt_trans hp.1 hp.2))
  · intro z _
    exact (ha.mul (hf.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _

@[simp] theorem panSumDensity_double (δ a f : ℝ → ℝ) (t : ℝ) :
    panSumDensity δ a f (2*t) = δ t/2 + 2 * ∫ s in 0..t, a s * f (2*t-s) := by
  simp [panSumDensity]

theorem panSumDensity_continuous {δ a f : ℝ → ℝ}
    (hδ : Continuous δ) (ha : Continuous a) (hf : Continuous f) :
    Continuous (panSumDensity δ a f) := by
  have hi : Continuous (fun z : ℝ => ∫ s in 0..z/2, a s * f (z-s)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((ha.comp continuous_snd).mul (hf.comp (continuous_fst.sub continuous_snd)))
      (continuous_id.div_const 2)
  exact ((hδ.comp (continuous_id.div_const 2)).div_const 2).add (continuous_const.mul hi)

theorem panSumDensity_congr_on {δ₁ a₁ f₁ δ₂ a₂ f₂ : ℝ → ℝ}
    (hd : EqOn δ₁ δ₂ (Ici 0)) (ha : EqOn a₁ a₂ (Ici 0))
    (hf : EqOn f₁ f₂ (Ici 0)) :
    EqOn (panSumDensity δ₁ a₁ f₁) (panSumDensity δ₂ a₂ f₂) (Ici 0) := by
  intro z hz
  have hz' : 0 ≤ z := hz
  unfold panSumDensity
  rw [hd (by change 0 ≤ z/2; positivity)]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by linarith : 0 ≤ z/2)] at hs
  change a₁ s*f₁ (z-s) = a₂ s*f₂ (z-s)
  rw [ha hs.1, hf (by change 0 ≤ z-s; linarith [hs.2])]

theorem continuous_clamp {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0)) :
    Continuous (fun t => g (max t 0)) :=
  hg.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)

theorem eqOn_clamp (g : ℝ → ℝ) : EqOn g (fun t => g (max t 0)) (Ici 0) := by
  intro t ht
  change g t = g (max t 0)
  rw [max_eq_left ht]

theorem panSumDensity_continuousOn {δ a f : ℝ → ℝ}
    (hδ : ContinuousOn δ (Ici 0)) (ha : ContinuousOn a (Ici 0))
    (hf : ContinuousOn f (Ici 0)) : ContinuousOn (panSumDensity δ a f) (Ici 0) := by
  exact (panSumDensity_continuous (continuous_clamp hδ) (continuous_clamp ha)
    (continuous_clamp hf)).continuousOn.congr
      (panSumDensity_congr_on (eqOn_clamp δ) (eqOn_clamp a) (eqOn_clamp f))

theorem panSumDensity_nonneg {δ a f : ℝ → ℝ}
    (hδ : ∀ t ≥ 0, 0 ≤ δ t) (ha : ∀ t ≥ 0, 0 ≤ a t) (hf : ∀ t ≥ 0, 0 ≤ f t)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ panSumDensity δ a f z := by
  unfold panSumDensity
  apply add_nonneg (div_nonneg (hδ _ (by positivity)) (by norm_num))
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by linarith : 0 ≤ z/2)
  intro s hs
  exact mul_nonneg (ha _ hs.1) (hf _ (by linarith [hs.2]))

theorem regularJointLaw_map_sum_pan_of_continuousOn (δ a f : ℝ → ℝ)
    (hδ : ContinuousOn δ (Ici 0)) (ha : ContinuousOn a (Ici 0))
    (hf : ContinuousOn f (Ici 0))
    (hδn : ∀ t ≥ 0, 0 ≤ δ t) (han : ∀ t ≥ 0, 0 ≤ a t)
    (hfn : ∀ t ≥ 0, 0 ≤ f t) :
    (regularJointLaw δ (fun p => a p.1 * f p.2)).map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z => ENNReal.ofReal (panSumDensity δ a
        f z)) := by
  have hd : diagonalDensityLaw δ = diagonalDensityLaw (fun t => δ (max t 0)) := by
    unfold diagonalDensityLaw
    congr 1
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [max_eq_left (le_of_lt ht)]
  have hj : triangularDensityLaw (fun p => a p.1 * f p.2) =
      triangularDensityLaw (fun p => a (max p.1 0)*f (max p.2 0)) := by
    unfold triangularDensityLaw
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
    rw [max_eq_left hp.1.le, max_eq_left (le_of_lt (lt_trans hp.1 hp.2))]
  have hl : regularJointLaw δ (fun p => a p.1 * f p.2) =
      regularJointLaw (fun t => δ (max t 0)) (fun p => a (max p.1 0)*f (max p.2 0)) := by
    simp only [regularJointLaw, hd, hj]
  rw [hl, regularJointLaw_map_sum_pan _ _ _ (continuous_clamp hδ).measurable
    (continuous_clamp ha) (continuous_clamp hf)
    (fun t _ => hδn _ (le_max_right t 0))
    (fun t _ => han _ (le_max_right t 0))
    (fun t _ => hfn _ (le_max_right t 0))]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [← panSumDensity_congr_on (eqOn_clamp δ) (eqOn_clamp a) (eqOn_clamp f)
    (Ioi_subset_Ici_self hz)]

theorem positive_density_identifies_on_halfline {g₁ g₂ : ℝ → ℝ}
    (h₁ : ContinuousOn g₁ (Ici 0)) (h₂ : ContinuousOn g₂ (Ici 0))
    (hn₁ : ∀ t ≥ 0, 0 ≤ g₁ t) (hn₂ : ∀ t ≥ 0, 0 ≤ g₂ t)
    (he : (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z => ENNReal.ofReal (g₁ z)) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z => ENNReal.ofReal (g₂ z))) :
    EqOn g₁ g₂ (Ici 0) := by
  have hc₁ := h₁.mono Ioi_subset_Ici_self
  have hc₂ := h₂.mono Ioi_subset_Ici_self
  have ha := (withDensity_eq_iff_of_sigmaFinite
    (hc₁.aemeasurable measurableSet_Ioi).ennreal_ofReal
    (hc₂.aemeasurable measurableSet_Ioi).ennreal_ofReal).mp he
  have hreal : g₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] g₂ := by
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with t ht hp
    exact (ENNReal.ofReal_eq_ofReal_iff (hn₁ _ hp.le) (hn₂ _ hp.le)).mp ht
  have heq := Measure.eqOn_open_of_ae_eq hreal isOpen_Ioi hc₁ hc₂
  exact heq.of_subset_closure h₁ h₂ Ioi_subset_Ici_self (by rw [closure_Ioi])

theorem sum_law_identifies_panSumDensity {δ₁ a₁ f₁ δ₂ a₂ f₂ : ℝ → ℝ}
    (hd₁ : ContinuousOn δ₁ (Ici 0)) (ha₁ : ContinuousOn a₁ (Ici 0))
    (hf₁ : ContinuousOn f₁ (Ici 0))
    (hd₂ : ContinuousOn δ₂ (Ici 0)) (ha₂ : ContinuousOn a₂ (Ici 0))
    (hf₂ : ContinuousOn f₂ (Ici 0))
    (hdn₁ : ∀ t ≥ 0, 0 ≤ δ₁ t) (han₁ : ∀ t ≥ 0, 0 ≤ a₁ t)
    (hfn₁ : ∀ t ≥ 0, 0 ≤ f₁ t)
    (hdn₂ : ∀ t ≥ 0, 0 ≤ δ₂ t) (han₂ : ∀ t ≥ 0, 0 ≤ a₂ t)
    (hfn₂ : ∀ t ≥ 0, 0 ≤ f₂ t)
    (he : (regularJointLaw δ₁ (fun p => a₁ p.1 * f₁ p.2)).map (fun p => p.1 + p.2) =
      (regularJointLaw δ₂ (fun p => a₂ p.1 * f₂ p.2)).map (fun p => p.1 + p.2)) :
    EqOn (panSumDensity δ₁ a₁ f₁) (panSumDensity δ₂ a₂ f₂) (Ici 0) := by
  rw [regularJointLaw_map_sum_pan_of_continuousOn _ _ _ hd₁ ha₁ hf₁ hdn₁ han₁ hfn₁,
    regularJointLaw_map_sum_pan_of_continuousOn _ _ _ hd₂ ha₂ hf₂ hdn₂ han₂ hfn₂] at he
  exact positive_density_identifies_on_halfline (panSumDensity_continuousOn hd₁ ha₁ hf₁)
    (panSumDensity_continuousOn hd₂ ha₂ hf₂)
    (fun _ ht => panSumDensity_nonneg hdn₁ han₁ hfn₁ ht)
    (fun _ ht => panSumDensity_nonneg hdn₂ han₂ hfn₂ ht) he

end Rhone.Statistics.Identifiability
