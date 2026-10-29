/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSamplePathRegularity

/-!
# Agreement of two positions from the segment of the first position

Source: wilton_carmi_hobolth2015, eq. (7). -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

theorem lintegral_Ioi_rate_exp_window {r s a b : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) *
        (ENNReal.ofReal s * (if a < t ∧ t ≤ b then
          ENNReal.ofReal (Real.exp (-((1 - s) * r * (b - t)))) else 0)) =
      ENNReal.ofReal (Real.exp (-((1 - s) * r * b + s * r * a)) - Real.exp (-(r * b))) := by
  let f : ℝ → ℝ := fun t => s * r * Real.exp (-(s * r) * t + -((1 - s) * r * b))
  let F : ℝ → ℝ := fun t => -Real.exp (-(s * r) * t + -((1 - s) * r * b))
  have hpt : ∀ t : ℝ, ENNReal.ofReal (r * Real.exp (-(r * t))) *
      (ENNReal.ofReal s * (if a < t ∧ t ≤ b then
        ENNReal.ofReal (Real.exp (-((1 - s) * r * (b - t)))) else 0)) =
      (Ioc a b).indicator (fun t => ENNReal.ofReal (f t)) t := by
    intro t
    by_cases hmem : a < t ∧ t ≤ b
    · rw [indicator_of_mem (show t ∈ Ioc a b from hmem)]
      simp only [hmem, and_self, ↓reduceIte]
      rw [← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_mul (mul_nonneg hr (Real.exp_nonneg _))]
      congr 1
      simp only [f]
      rw [show -(s * r) * t + -((1 - s) * r * b) = -(r * t) + -((1 - s) * r * (b - t)) by
        ring, Real.exp_add]
      ring
    · rw [indicator_of_notMem (show t ∉ Ioc a b from hmem)]
      simp only [hmem, ↓reduceIte, mul_zero]
  have hF : ∀ t : ℝ, HasDerivAt F (f t) t := by
    intro t
    have h1 := (hasDerivAt_exp_affine (-(s * r)) (-((1 - s) * r * b)) t).neg
    convert h1 using 1
    simp only [f]
    ring
  have hf : Continuous f := by fun_prop
  have hsub : Ioc a b ⊆ Ioi 0 := fun t ht => ha.trans_lt ht.1
  rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub,
    ← setLIntegral_congr Ioo_ae_eq_Ioc,
    lintegral_Ioo_ofReal_of_hasDerivAt hab hF hf
      (fun t _ => mul_nonneg (mul_nonneg hs hr) (Real.exp_nonneg _))]
  congr 1
  simp only [F]
  rw [show -(s * r) * b + -((1 - s) * r * b) = -(r * b) by ring,
    show -(s * r) * a + -((1 - s) * r * b) = -((1 - s) * r * b + s * r * a) by ring]
  ring

noncomputable def agreeTerm (x y : ℝ) (n : ℕ) (ω : ℕ → SpatialState 2) : ℝ≥0∞ :=
  (if (ω 0).1 ≤ x ∧ x < (ω 1).1 then 1 else 0) * heldTerm y (rootHeight (ω 0).2) n ω

theorem measurable_agreeTerm (x y : ℝ) (n : ℕ) : Measurable (agreeTerm x y n) := by
  unfold agreeTerm heldTerm
  have hp : ∀ i : ℕ, Measurable fun ω : ℕ → SpatialState 2 => (ω i).1 := fun i =>
    measurable_fst.comp (measurable_pi_apply i)
  have hH : ∀ i : ℕ, Measurable fun ω : ℕ → SpatialState 2 => rootHeight (ω i).2 := fun i =>
    (rootHeight_measurable 2).comp (measurable_snd.comp (measurable_pi_apply i))
  refine Measurable.mul ?_
    ((Measurable.mul ?_ ?_).mul (Finset.measurable_prod _ fun j _ => ?_))
  · exact Measurable.ite ((measurableSet_le (hp 0) measurable_const).inter
      (measurableSet_lt measurable_const (hp 1))) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le (hp n) measurable_const) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const (hp (n + 1))) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_eq_fun (hH j) (hH 0)) measurable_const
      measurable_const

theorem agreeTerm_streamCons_zero {x y : ℝ} (hxy : x ≤ y) (z : SpatialState 2)
    (hzx : z.1 ≤ x) (ω' : ℕ → SpatialState 2) :
    agreeTerm x y 0 (streamCons (z, ω')) = if y < (ω' 0).1 then 1 else 0 := by
  unfold agreeTerm
  rw [heldTerm_streamCons_zero]
  change (if z.1 ≤ x ∧ x < (ω' 0).1 then (1 : ℝ≥0∞) else 0) *
    ((if z.1 ≤ y then 1 else 0) * (if rootHeight z.2 = rootHeight z.2 then 1 else 0) *
      (if y < (ω' 0).1 then 1 else 0)) = _
  by_cases h : y < (ω' 0).1
  · simp only [hzx, hzx.trans hxy, hxy.trans_lt h, h, and_self, ↓reduceIte, mul_one]
  · simp only [h, ↓reduceIte, mul_zero]

theorem agreeTerm_streamCons_succ (x y : ℝ) (n : ℕ) (z : SpatialState 2)
    (ω' : ℕ → SpatialState 2) :
    agreeTerm x y (n + 1) (streamCons (z, ω')) =
      (if z.1 ≤ x ∧ x < (ω' 0).1 then 1 else 0) * heldTerm y (rootHeight z.2) n ω' := by
  unfold agreeTerm
  rw [heldTerm_streamCons_succ]
  change (if z.1 ≤ x ∧ x < (ω' 0).1 then (1 : ℝ≥0∞) else 0) *
    ((if rootHeight z.2 = rootHeight z.2 then 1 else 0) *
      heldTerm y (rootHeight z.2) n ω') = _
  simp only [↓reduceIte, one_mul]

theorem agreeTerm_streamCons_of_not_le {x : ℝ} (y : ℝ) (n : ℕ) (z : SpatialState 2)
    (hzx : ¬ z.1 ≤ x) (ω' : ℕ → SpatialState 2) :
    agreeTerm x y n (streamCons (z, ω')) = 0 := by
  unfold agreeTerm
  change (if z.1 ≤ x ∧ x < (ω' 0).1 then (1 : ℝ≥0∞) else 0) * _ = 0
  simp only [hzx, false_and, ↓reduceIte, zero_mul]

/-- Source: wilton_carmi_hobolth2015, eq. (7). -/
theorem spatialProcess_two_agreeTerm_tsum {R : ℝ} (hR : 0 < R) {x y : ℝ} (hxy : x ≤ y)
    (hy : y < 1) (z : SpatialState 2) (hz : TwoSampleArray z.2) (hh : 0 < rootHeight z.2) :
    ∑' n, ∫⁻ ω, agreeTerm x y n ω ∂(spatialProcess 2 R).pathLaw z =
      if z.1 ≤ x then
        ENNReal.ofReal (Real.exp (-(R * rootHeight z.2 * (x - z.1)))) *
          ENNReal.ofReal (Real.exp
              (-(R * Analysis.SmcPrime.smcPrimeLambda (rootHeight z.2) * (y - x))))
      else 0 := by
  obtain ⟨p, T⟩ := z
  dsimp only at hz hh ⊢
  have hfirst : ∀ n, ∫⁻ ω, agreeTerm x y n ω ∂(spatialProcess 2 R).pathLaw (p, T) =
      ∫⁻ a, ∫⁻ ω', agreeTerm x y n (streamCons ((p, T), ω'))
        ∂(spatialProcess 2 R).pathLaw (spatialStep 2 R (p, T) a) ∂proposalNoiseLaw :=
    fun n => spatialProcess_pathLaw_lintegral_first_step 2 R _ _ (measurable_agreeTerm x y n)
  simp only [hfirst]
  by_cases hpx : p ≤ x
  swap
  · simp only [hpx, ↓reduceIte, agreeTerm_streamCons_of_not_le y _ (p, T) hpx,
      lintegral_zero, tsum_zero]
  simp only [hpx, ↓reduceIte]
  have hp1 : p < 1 := hpx.trans_lt (hxy.trans_lt hy)
  have hRh : 0 < R * rootHeight T := mul_pos hR hh
  have hs : 0 ≤ twoSampleSelfMass (rootHeight T) := twoSampleSelfMass_nonneg hh
  have hstepm : Measurable fun a : ProposalNoise => spatialStep 2 R (p, T) a :=
    (spatialStep_measurable 2 R).comp (measurable_const.prodMk measurable_id)
  have hcons : Measurable fun ω' : ℕ → SpatialState 2 => streamCons ((p, T), ω') :=
    measurable_streamCons.comp (measurable_const.prodMk measurable_id)
  have hmeas : ∀ n, Measurable fun a : ProposalNoise =>
      ∫⁻ ω', agreeTerm x y n (streamCons ((p, T), ω'))
        ∂(spatialProcess 2 R).pathLaw (spatialStep 2 R (p, T) a) := by
    intro n
    have h0 : Measurable fun w : SpatialState 2 =>
        ∫⁻ ω', agreeTerm x y n (streamCons ((p, T), ω')) ∂(spatialProcess 2 R).traj w :=
      ((measurable_agreeTerm x y n).comp hcons).lintegral_kernel
    exact h0.comp hstepm
  rw [← lintegral_tsum fun n => (hmeas n).aemeasurable]
  let Ψ : ℝ × ℝ → ℝ≥0∞ := fun q =>
    if x < q.1 ∧ q.2 = rootHeight T ∧ q.1 ≤ y then
      ENNReal.ofReal (Real.exp (-(R * Analysis.SmcPrime.smcPrimeLambda (rootHeight T) * (y - q.1))))
    else 0
  have hΨ : Measurable Ψ := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_eq_fun measurable_snd measurable_const).inter
          (measurableSet_le measurable_fst measurable_const))
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hae : ∀ᵐ a ∂proposalNoiseLaw,
      ∑' n, ∫⁻ ω', agreeTerm x y n (streamCons ((p, T), ω'))
        ∂(spatialProcess 2 R).pathLaw (spatialStep 2 R (p, T) a) =
      (if y < (spatialStep 2 R (p, T) a).1 then (1 : ℝ≥0∞) else 0) +
        Ψ ((spatialStep 2 R (p, T) a).1, rootHeight (spatialStep 2 R (p, T) a).2) := by
    filter_upwards [hz.spatialStep_good_ae R hh p] with a ha
    generalize spatialStep 2 R (p, T) a = w at ha ⊢
    rw [tsum_eq_zero_add' ENNReal.summable]
    have e0 : ∫⁻ ω', agreeTerm x y 0 (streamCons ((p, T), ω'))
        ∂(spatialProcess 2 R).pathLaw w = if y < w.1 then 1 else 0 := by
      simp only [agreeTerm_streamCons_zero hxy (p, T) hpx]
      exact spatialProcess_pathLaw_lintegral_eval_zero 2 R w
        (fun v : SpatialState 2 => if y < v.1 then (1 : ℝ≥0∞) else 0)
        (Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
          measurable_const)
    have es : ∀ n, ∫⁻ ω', agreeTerm x y (n + 1) (streamCons ((p, T), ω'))
        ∂(spatialProcess 2 R).pathLaw w =
        (if x < w.1 then 1 else 0) *
          ∫⁻ ω', heldTerm y (rootHeight T) n ω' ∂(spatialProcess 2 R).pathLaw w := by
      intro n
      simp only [agreeTerm_streamCons_succ]
      by_cases hw : x < w.1
      · have h0 := spatialProcess_pathLaw_ae_eval_zero 2 R w {v | x < v.1}
          (measurableSet_lt measurable_const measurable_fst) hw
        simp only [hw, ↓reduceIte, one_mul]
        refine lintegral_congr_ae ?_
        filter_upwards [h0] with ω' hω'
        have hω'' : x < (ω' 0).1 := hω'
        simp only [hpx, hω'', and_self, ↓reduceIte, one_mul]
      · have h0 := spatialProcess_pathLaw_ae_eval_zero 2 R w {v | x < v.1}ᶜ
          (measurableSet_lt measurable_const measurable_fst).compl hw
        simp only [hw, ↓reduceIte, zero_mul]
        refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
        filter_upwards [h0] with ω' hω'
        have hω'' : ¬ x < (ω' 0).1 := hω'
        simp only [hω'', and_false, ↓reduceIte, zero_mul]
    rw [e0]
    simp only [es]
    rw [ENNReal.tsum_mul_left, spatialProcess_two_noChange hR hy _ w ha.1 ha.2]
    congr 1
    by_cases hw : x < w.1
    · simp only [Ψ, hw, true_and, ↓reduceIte, one_mul]
    · simp only [Ψ, hw, false_and, ↓reduceIte, zero_mul]
  have hm1 : Measurable fun a : ProposalNoise =>
      if y < (spatialStep 2 R (p, T) a).1 then (1 : ℝ≥0∞) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp hstepm))
      measurable_const measurable_const
  rw [lintegral_congr_ae hae, lintegral_add_left hm1,
    hz.spatialStep_position_gt_lintegral hR hh (hpx.trans hxy) hy,
    hz.spatialStep_lintegral hR hh hp1 Ψ hΨ]
  have hzero : ∀ d : ℝ, ∫⁻ a in Ioi 0,
      ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) * Ψ (d, a) = 0 := by
    intro d
    refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (rootHeight T))] with a ha
    simp only [Ψ, ha, false_and, and_false, ↓reduceIte, mul_zero]
  let G : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
      (if x - p < t ∧ t ≤ y - p then
        ENNReal.ofReal (Real.exp (-((1 - twoSampleSelfMass (rootHeight T)) *
          (R * rootHeight T) * (y - p - t))))
      else 0)
  have hG : Measurable G := by
    refine Measurable.const_mul (Measurable.ite ?_ ?_ measurable_const) _
    · exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_le measurable_id measurable_const)
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hΨt : ∀ t : ℝ, ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
      Ψ (p + t, rootHeight T) = G t := by
    intro t
    have i1 : x < p + t ↔ x - p < t := sub_lt_iff_lt_add'.symm
    have i2 : p + t ≤ y ↔ t ≤ y - p := le_sub_iff_add_le'.symm
    have harg : R * Analysis.SmcPrime.smcPrimeLambda (rootHeight T) * (y - (p + t)) =
        (1 - twoSampleSelfMass (rootHeight T)) * (R * rootHeight T) * (y - p - t) := by
      rw [← mul_one_sub_twoSampleSelfMass hh]
      ring
    simp only [Ψ, G, true_and, i1, i2, harg]
  have h1y : ¬ (1 : ℝ) ≤ y := not_le.mpr hy
  have hpt : ∀ e ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-e)) *
      (if p + e / (R * rootHeight T) < 1 then
        ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
            Ψ (p + e / (R * rootHeight T), rootHeight T) +
          ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
            Ψ (p + e / (R * rootHeight T), a)
      else Ψ (1, rootHeight T)) =
      ENNReal.ofReal (Real.exp (-e)) * G (e / (R * rootHeight T)) := by
    intro e _
    congr 1
    by_cases h1 : p + e / (R * rootHeight T) < 1
    · simp only [h1, ↓reduceIte, hzero, add_zero, hΨt]
    · have h2 : ¬ e / (R * rootHeight T) ≤ y - p := fun h =>
        h1 ((le_sub_iff_add_le'.mp h).trans_lt hy)
      simp only [h1, ↓reduceIte, Ψ, G, h1y, h2, and_false, mul_zero]
  have hwin : ∫⁻ t in Ioi 0,
      ENNReal.ofReal (R * rootHeight T * Real.exp (-(R * rootHeight T * t))) * G t =
      ENNReal.ofReal (Real.exp (-((1 - twoSampleSelfMass (rootHeight T)) *
          (R * rootHeight T) * (y - p) +
        twoSampleSelfMass (rootHeight T) * (R * rootHeight T) * (x - p))) -
          Real.exp (-(R * rootHeight T * (y - p)))) :=
    lintegral_Ioi_rate_exp_window hRh.le hs (sub_nonneg.mpr hpx) (sub_le_sub_right hxy p)
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_Ioi_exp_neg_comp_div hRh G hG,
    hwin]
  have hk : twoSampleSelfMass (rootHeight T) * (R * rootHeight T) * (x - p) ≤
      twoSampleSelfMass (rootHeight T) * (R * rootHeight T) * (y - p) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hxy p) (mul_nonneg hs hRh.le)
  have hle : -(R * rootHeight T * (y - p)) ≤
      -((1 - twoSampleSelfMass (rootHeight T)) * (R * rootHeight T) * (y - p) +
        twoSampleSelfMass (rootHeight T) * (R * rootHeight T) * (x - p)) := by
    nlinarith [hk]
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (sub_nonneg.mpr (Real.exp_le_exp.mpr hle)),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_sub_cancel]
  congr 2
  rw [← mul_one_sub_twoSampleSelfMass hh]
  ring

end Rhone.Coalescent.SmcPrime
