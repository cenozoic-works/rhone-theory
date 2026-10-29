/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanLaw
public import Rhone.Statistics.Identifiability.IntegrablePanLaplaceIntegral
public import Rhone.Statistics.Identifiability.MutationPulseKernel

/-! # Backward-value check for locally integrable pan rates -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Matrix
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem ac_flux_integral_Ioi {F g : ℝ → ℝ} {a : ℝ}
    (hac : ∀ b, a ≤ b → AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ x, a ≤ x → HasDerivAt F (-g x) x)
    (hn : ∀ᵐ x, a ≤ x → 0 ≤ g x)
    (hm : AEMeasurable g (volume.restrict (Ioi a)))
    (htail : Tendsto F atTop (𝓝 0)) :
    0 ≤ F a ∧ IntegrableOn g (Ioi a) ∧ (∫ x in Ioi a, g x) = F a := by
  have hFa : 0 ≤ F a := by
    apply le_of_tendsto htail
    filter_upwards [eventually_ge_atTop a] with b hb
    apply ac_endpoint_le_of_ae_hasDerivAt_nonpos hb (hac b hb)
    · filter_upwards [hd] with x hx hmem
      exact hx ((by simpa only [uIcc_of_le hb, mem_Icc] using hmem : a ≤ x ∧ x ≤ b).1)
    · filter_upwards [hn] with x hx hmem
      exact neg_nonpos.mpr (hx ((by simpa only [uIcc_of_le hb, mem_Icc] using hmem : a ≤ x ∧ x ≤
        b).1))
  have hn' : ∀ᵐ x ∂volume.restrict (Ioi a), 0 ≤ g x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hn] with x hx hxmem
    exact hx hxmem.le
  have hl := ac_flux_lintegral_Ioi hac hd hn hm htail
  simp only [sub_zero] at hl
  refine ⟨hFa, ⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hn', hl]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hn' hm.aestronglyMeasurable, hl,
      ENNReal.toReal_ofReal hFa]

theorem bounded_discount_tendsto_zero {f : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hf : ∃ M : ℝ, ∀ t, 0 ≤ t → |f t| ≤ M) :
    Tendsto (fun t => Real.exp (-k * t) * f t) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-k * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hk)).mpr
      tendsto_id)
  obtain ⟨M, hM⟩ := hf
  have hb : IsBoundedUnder (· ≤ ·) atTop (norm ∘ f) := by
    apply isBoundedUnder_of_eventually_le (a := M)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hM t ht
  exact NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded he hb

theorem killed_pair_weight_tendsto_zero {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) {k s : ℝ} (hk : 0 < k) (hs : 0 ≤ s) :
    Tendsto (fun t => Real.exp (integrablePanClock rate s - integrablePanClock rate t -
      k * (t - s))) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-k * (t-s))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply (tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hk)).mpr
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atTop_add_const_right atTop (-s) tendsto_id)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · exact Eventually.of_forall (fun t => (Real.exp_pos _).le)
  · filter_upwards [eventually_ge_atTop s] with t ht
    apply Real.exp_le_exp.mpr
    have hmono := integrablePanClock_monotoneOn hr hrn hs (hs.trans ht) ht
    linarith

theorem bounded_pair_backward_eq_integral {rate v : ℝ → ℝ} {k : ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) (hk : 0 < k)
    (hvac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval v 0 T)
    (hvd : ∀ᵐ t, 0 ≤ t → HasDerivAt v ((rate t + k) * v t - rate t) t)
    (hvb : ∃ M : ℝ, ∀ t, 0 ≤ t → |v t| ≤ M)
    {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ v s ∧
    IntegrableOn (fun t => rate t * Real.exp (integrablePanClock rate s -
      integrablePanClock rate t - k * (t-s))) (Ioi s) ∧
    v s = ∫ t in Ioi s, rate t * Real.exp (integrablePanClock rate s -
      integrablePanClock rate t - k * (t-s)) := by
  let H := integrablePanClock rate
  let w := fun t => Real.exp (H s - H t - k * (t-s))
  let F := fun t => w t * v t
  let g := fun t => rate t * w t
  have hac (b : ℝ) (hb : s ≤ b) : AbsolutelyContinuousOnInterval F s b := by
    apply AbsolutelyContinuousOnInterval.mul
    · apply ac_exp
      exact (((LipschitzWith.const (H s)).lipschitzOnWith.absolutelyContinuousOnInterval).sub
        (integrablePanClock_ac hr s b)).sub
        (((LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).sub
          (LipschitzWith.const s).lipschitzOnWith.absolutelyContinuousOnInterval).const_mul k)
    · exact (hvac b (hs.trans hb)).mono (uIcc_subset_uIcc
        (by simpa [uIcc_of_le (hs.trans hb)] using And.intro hs hb) (by simp))
  have hd : ∀ᵐ t, s ≤ t → HasDerivAt F (-g t) t := by
    filter_upwards [integrablePanClock_ae_hasDerivAt hr, hvd] with t ht hvt hst
    have hw := (((ht (hs.trans hst)).const_sub (H s)).sub
      (((hasDerivAt_id t).sub_const s).const_mul k)).exp
    convert! hw.mul (hvt (hs.trans hst)) using 1
    dsimp [F, g, w, H]
    ring
  have hn : ∀ᵐ t, s ≤ t → 0 ≤ g t := by
    filter_upwards [hrn] with t ht hst
    exact mul_nonneg (ht (hs.trans hst)) (Real.exp_pos _).le
  have hm : AEMeasurable g (volume.restrict (Ioi s)) := by
    exact (hr.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono (fun t ht => hs.trans ht.le) le_rfl)).mul
      ((Real.continuous_exp.comp ((continuous_const.sub (integrablePanClock_continuous hr)).sub
        (continuous_const.mul (continuous_id.sub continuous_const)))).measurable.aemeasurable)
  have htail : Tendsto F atTop (𝓝 0) := by
    obtain ⟨M, hM⟩ := hvb
    have hb : IsBoundedUnder (· ≤ ·) atTop (norm ∘ v) := by
      apply isBoundedUnder_of_eventually_le (a := M)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simpa only [Function.comp_apply, Real.norm_eq_abs] using hM t ht
    exact NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      (killed_pair_weight_tendsto_zero hr hrn hk hs) hb
  have h := ac_flux_integral_Ioi hac hd hn hm htail
  simpa only [F, w, H, g, sub_self, mul_zero, Real.exp_zero, one_mul] using
    And.intro h.1 (And.intro h.2.1 h.2.2.symm)

structure IntegrablePanBackwardValue (rate recomb : ℝ → ℝ) (k : ℝ) where
  val : ℝ → MutationPulseKernel.State → ℝ
  ac : ∀ T, 0 ≤ T → ∀ i, AbsolutelyContinuousOnInterval (fun t => val t i) 0 T
  bounded : ∃ M : ℝ, ∀ t, 0 ≤ t → ∀ i, |val t i| ≤ M
  absorbing : ∀ t, 0 ≤ t → val t 4 = 1
  equation : ∀ᵐ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => val s i)
    (-(MutationPulseKernel.B (rate t) (recomb t) k *ᵥ val t) i) t

namespace IntegrablePanBackwardValue
variable {rate recomb : ℝ → ℝ} {k : ℝ} (V : IntegrablePanBackwardValue rate recomb k)

theorem val_aemeasurable (i : MutationPulseKernel.State) :
    AEMeasurable (fun t => V.val t i) (volume.restrict (Ioi 0)) :=
  ((halfLineAC_continuousOn (fun T hT => V.ac T hT i)).aestronglyMeasurable
    measurableSet_Ici).aemeasurable.mono_measure
      (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)

theorem coordinate_equations : ∀ᵐ t, 0 ≤ t →
    HasDerivAt (fun s => V.val s 0)
      ((rate t + 2 * recomb t + 2*k) * V.val t 0 - 2*recomb t * V.val t 1 - rate t) t ∧
    HasDerivAt (fun s => V.val s 1)
      (-rate t * V.val t 0 + (3*rate t + recomb t + 2*k) * V.val t 1 -
        recomb t * V.val t 2 - 2*rate t * V.val t 3) t ∧
    HasDerivAt (fun s => V.val s 2)
      (-4*rate t * V.val t 1 + (6*rate t + 2*k) * V.val t 2 - 2*rate t * V.val t 3) t ∧
    HasDerivAt (fun s => V.val s 3) ((rate t + k) * V.val t 3 - rate t) t := by
  filter_upwards [V.equation] with t ht ht0
  have hh := ht ht0
  have h4 := V.absorbing t ht0
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  simp only [Fin.isValue, Matrix.mulVec, dotProduct, MutationPulseKernel.B, MutationPulseKernel.G,
      MutationPulseKernel.C, Matrix.smul_of, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one,
    mul_zero, Matrix.smul_empty,
      MutationPulseKernel.R, Matrix.of_add_of, Matrix.add_cons, Matrix.head_cons,
    Matrix.tail_cons, zero_add, add_zero,
      Matrix.empty_add_empty, MutationPulseKernel.D, MutationPulseKernel.d, Matrix.sub_apply,
    Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.smul_apply,
    Fin.sum_univ_succ,
      Matrix.diagonal_apply_eq, Matrix.cons_val_succ, Fin.succ_zero_eq_one, ne_eq, zero_ne_one,
    not_false_eq_true,
      Matrix.diagonal_apply_ne, sub_zero, Fin.succ_one_eq_two, Fin.reduceEq, sub_self, zero_mul,
    Fin.reduceSucc,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, h4, neg_add_rev,
    Matrix.cons_val_one, one_ne_zero,
      zero_sub, neg_mul, Finset.sum_neg_distrib, neg_zero, Matrix.cons_val] at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! h0 using 1
    ring
  · convert! h1 using 1
    ring
  · convert! h2 using 1
    ring
  · convert! h3 using 1
    ring

theorem pair_integral (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ V.val s 3 ∧
    IntegrableOn (fun t => rate t * Real.exp (integrablePanClock rate s -
      integrablePanClock rate t - k * (t-s))) (Ioi s) ∧
    V.val s 3 = ∫ t in Ioi s, rate t * Real.exp (integrablePanClock rate s -
      integrablePanClock rate t - k * (t-s)) := by
  apply bounded_pair_backward_eq_integral hr hrn hk (fun T hT => V.ac T hT 3)
  · filter_upwards [V.coordinate_equations] with t ht ht0
    exact (ht ht0).2.2.2
  · obtain ⟨M, hM⟩ := V.bounded
    exact ⟨M, fun t ht => hM t ht 3⟩
  · exact hs

theorem pair_lintegral (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (rate t * Real.exp (integrablePanClock rate s -
      integrablePanClock rate t - k * (t-s)))) = ENNReal.ofReal (V.val s 3) := by
  obtain ⟨_, hi, he⟩ := V.pair_integral hr hrn hk hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi, ← he]
  change ∀ᵐ t ∂volume.restrict (Ioi s), 0 ≤ rate t * Real.exp
    (integrablePanClock rate s - integrablePanClock rate t - k * (t-s))
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hrn] with t ht hst
  exact mul_nonneg (ht (hs.trans hst.le)) (Real.exp_pos _).le

theorem pairLaw_laplace_lintegral
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t, ENNReal.ofReal (Real.exp (-k*(t-s)))
      ∂conditionalPairLaw rate (integrablePanClock rate) s) =
      ENNReal.ofReal (V.val s 3) := by
  have hm : AEMeasurable (conditionalPairDensity rate (integrablePanClock rate) s)
      (volume.restrict (Ioi s)) :=
    (hr.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono (fun t ht => hs.trans ht.le) le_rfl)).mul
        ((Real.continuous_exp.comp (continuous_const.sub
          (integrablePanClock_continuous hr))).measurable.aemeasurable)
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-k*(t-s)))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub
      continuous_const))).measurable.ennreal_ofReal
  rw [conditionalPairLaw, lintegral_withDensity_eq_lintegral_mul₀ hm.ennreal_ofReal
    hw.aemeasurable]
  rw [← V.pair_lintegral hr hrn hk hs]
  apply lintegral_congr_ae
  filter_upwards [hrn.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t ht hst
  have hden : 0 ≤ conditionalPairDensity rate (integrablePanClock rate) s t :=
    mul_nonneg (ht (hs.trans hst.le)) (Real.exp_pos _).le
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hden]
  congr 1
  unfold conditionalPairDensity
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem pairLaw_laplace_integral
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ t, Real.exp (-k*(t-s))
      ∂conditionalPairLaw rate (integrablePanClock rate) s) = V.val s 3 := by
  have hw : Measurable (fun t : ℝ => Real.exp (-k*(t-s))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub
      continuous_const))).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun t => (Real.exp_pos _).le))
    hw.aestronglyMeasurable,
    V.pairLaw_laplace_lintegral hr hrn hk hs,
    ENNReal.toReal_ofReal (V.pair_integral hr hrn hk hs).1]

end IntegrablePanBackwardValue

namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate) {k : ℝ}
variable (V : IntegrablePanBackwardValue rate P.recomb k)

noncomputable def backwardPairing (t : ℝ) : ℝ :=
  Real.exp (-2*k*t) * (P.D t * V.val t 0 + P.R t * V.val t 1 + P.U t * V.val t 2)

noncomputable def backwardFlux (t : ℝ) : ℝ :=
  Real.exp (-2*k*t) * (rate t * P.D t + 2 * rate t * P.nonDiagonal t * V.val t 3)

@[simp] theorem backwardPairing_zero : P.backwardPairing V 0 = V.val 0 0 := by
  simp [backwardPairing, P.initial]

theorem backwardPairing_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (P.backwardPairing V) (-P.backwardFlux V t) t := by
  filter_upwards [P.equations, V.coordinate_equations] with t hP hV ht0
  obtain ⟨hD, hR, hU⟩ := hP ht0
  obtain ⟨hv0, hv1, hv2, _⟩ := hV ht0
  have he := ((hasDerivAt_id t).const_mul (-2*k)).exp
  have hp := ((hD.mul hv0).add (hR.mul hv1)).add (hU.mul hv2)
  convert! he.mul hp using 1
  dsimp [backwardFlux, nonDiagonal]
  ring

theorem backwardPairing_ac {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (P.backwardPairing V) 0 T :=
  (ac_exp ((LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).const_mul
    (-2*k))).mul
    (((P.D_ac T hT).mul (V.ac T hT 0)).fun_add
      ((P.R_ac T hT).mul (V.ac T hT 1)) |>.fun_add ((P.U_ac T hT).mul (V.ac T hT 2)))

theorem backwardPairing_tendsto_zero (hk : 0 < k) :
    Tendsto (P.backwardPairing V) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := V.bounded
  have hMn : 0 ≤ M := (abs_nonneg (V.val 0 0)).trans (hM 0 le_rfl 0)
  have hbound : ∀ t, 0 ≤ t →
      |P.D t * V.val t 0 + P.R t * V.val t 1 + P.U t * V.val t 2| ≤ M := by
    intro t ht
    have hD := (P.D_positive t ht).le
    have hR := P.R_nonneg t ht
    have hU := P.U_nonneg t ht
    calc
      _ ≤ |P.D t * V.val t 0 + P.R t * V.val t 1| + |P.U t * V.val t 2| := abs_add_le _ _
      _ ≤ |P.D t * V.val t 0| + |P.R t * V.val t 1| + |P.U t * V.val t 2| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = P.D t * |V.val t 0| + P.R t * |V.val t 1| + P.U t * |V.val t 2| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hD, abs_of_nonneg hR, abs_of_nonneg hU]
      _ ≤ P.D t * M + P.R t * M + P.U t * M := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hM t ht 0) hD)
          (mul_le_mul_of_nonneg_left (hM t ht 1) hR)) (mul_le_mul_of_nonneg_left (hM t ht 2) hU)
      _ = P.total t * M := by unfold total; ring
      _ ≤ M := by simpa using mul_le_mul_of_nonneg_right (P.total_le_one ht) hMn
  have hh := bounded_discount_tendsto_zero (show 0 < 2*k by positivity) ⟨M, hbound⟩
  convert! hh using 1
  ext t
  dsimp [backwardPairing]
  congr 2
  ring

theorem backwardFlux_integral (hk : 0 < k) :
    0 ≤ V.val 0 0 ∧ IntegrableOn (P.backwardFlux V) (Ioi 0) ∧
    (∫ t in Ioi 0, P.backwardFlux V t) = V.val 0 0 := by
  have hn : ∀ᵐ t, 0 ≤ t → 0 ≤ P.backwardFlux V t := by
    filter_upwards [P.rate_nonneg] with t ht ht0
    have hv := (V.pair_integral P.rate_integrable P.rate_nonneg hk ht0).1
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg
      (mul_nonneg (ht ht0) (P.D_positive t ht0).le)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (ht ht0))
        (P.nonDiagonal_nonneg ht0)) hv))
  have hm : AEMeasurable (P.backwardFlux V) (volume.restrict (Ioi 0)) := by
    have hv : AEMeasurable (fun t => V.val t 3) (volume.restrict (Ioi 0)) :=
      ((halfLineAC_continuousOn (fun T hT => V.ac T hT 3)).aestronglyMeasurable
        measurableSet_Ici).aemeasurable.mono_measure
          (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)
    have hx := P.diagonalDensity_aemeasurable.add
      ((P.nonDiagonalFlux_aemeasurable.const_mul 2).mul hv)
    have hmexp : AEMeasurable (fun t : ℝ => Real.exp (-2*k*t)) (volume.restrict (Ioi 0)) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.aemeasurable
    convert! hmexp.mul hx using 1
    ext t
    dsimp [backwardFlux, diagonalDensity]
    ring
  simpa only [P.backwardPairing_zero] using ac_flux_integral_Ioi
    (fun b hb => P.backwardPairing_ac V hb) (P.backwardPairing_ae_hasDerivAt V) hn hm
      (P.backwardPairing_tendsto_zero V hk)

theorem backwardFlux_lintegral (hk : 0 < k) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (P.backwardFlux V t)) =
      ENNReal.ofReal (V.val 0 0) := by
  obtain ⟨_, hi, he⟩ := P.backwardFlux_integral V hk
  rw [← ofReal_integral_eq_lintegral_ofReal hi, he]
  change ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ P.backwardFlux V t
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [P.rate_nonneg] with t ht ht0
  have hv := (V.pair_integral P.rate_integrable P.rate_nonneg hk ht0.le).1
  exact mul_nonneg (Real.exp_pos _).le (add_nonneg
    (mul_nonneg (ht ht0.le) (P.D_positive t ht0.le).le)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (ht ht0.le))
      (P.nonDiagonal_nonneg ht0.le)) hv))

theorem backwardValue_jointLaplace_lintegral (hk : 0 < k) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (-k*(p.1+p.2))) ∂P.jointLaw) =
      ENNReal.ofReal (V.val 0 0) := by
  have hn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ V.val t 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (V.pair_integral P.rate_integrable P.rate_nonneg hk ht.le).1
  have hker : ∀ᵐ s ∂volume.restrict (Ioi 0),
      (∫⁻ t in Ioi s, ENNReal.ofReal (rate t * Real.exp (integrablePanClock rate s -
        integrablePanClock rate t - k*(t-s)))) = ENNReal.ofReal (V.val s 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact V.pair_lintegral P.rate_integrable P.rate_nonneg hk hs.le
  rw [P.jointLaw_laplace_lintegral k (fun t => V.val t 3) (V.val_aemeasurable 3) hn hker]
  convert! P.backwardFlux_lintegral V hk using 1
  congr 1
  ext t
  congr 1
  dsimp [backwardFlux, diagonalDensity]
  ring

include V in
theorem backwardValue_jointLaplace_integrable (hk : 0 < k) :
    Integrable (fun p => Real.exp (-k*(p.1+p.2))) P.jointLaw := by
  refine ⟨(Real.measurable_exp.comp ((measurable_fst.add measurable_snd).const_mul
    (-k))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p => (Real.exp_pos _).le)),
    P.backwardValue_jointLaplace_lintegral V hk]
  exact ENNReal.ofReal_lt_top

theorem backwardValue_jointLaplace_integral (hk : 0 < k) :
    (∫ p, Real.exp (-k*(p.1+p.2)) ∂P.jointLaw) = V.val 0 0 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun p => (Real.exp_pos _).le))
    (P.backwardValue_jointLaplace_integrable V hk).aestronglyMeasurable,
    P.backwardValue_jointLaplace_lintegral V hk,
    ENNReal.toReal_ofReal (P.backwardFlux_integral V hk).1]

end IntegrablePanPreModel

theorem ProperIntegrablePanModel.backwardValue_singleLaplace_integral
    (P : ProperIntegrablePanModel) {k : ℝ}
    (V : IntegrablePanBackwardValue P.rate P.pre.recomb k) (hk : 0 < k) :
    (∫ p, Real.exp (-k*p.1) ∂P.pre.jointLaw) = V.val 0 3 := by
  have hm : AEStronglyMeasurable (fun t : ℝ => Real.exp (-k*t))
      (P.pre.jointLaw.map Prod.fst) :=
    (Real.measurable_exp.comp (measurable_id.const_mul (-k))).aestronglyMeasurable
  rw [← integral_map measurable_fst.aemeasurable hm, P.jointLaw_map_fst]
  simpa only [sub_zero] using V.pairLaw_laplace_integral P.pre.rate_integrable
    P.pre.rate_nonneg hk (s := 0) le_rfl

end Rhone.Statistics.Identifiability
