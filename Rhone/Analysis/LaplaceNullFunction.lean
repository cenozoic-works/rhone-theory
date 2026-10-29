/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # A nonzero bounded continuous function with vanishing Laplace transforms at `k(k-1)/2` -/

@[expose] public section

namespace Rhone.Analysis

open MeasureTheory Set Filter Complex
open scoped Topology FourierTransform

theorem hasDerivAt_cexp_neg_div {w : ℂ} (hw : w ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => cexp (-w / s) / w) (cexp (-w / t) / (t : ℂ) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) (((-(t ^ 2)⁻¹ : ℝ)) : ℂ) t :=
    (hasDerivAt_inv ht).ofReal_comp
  have h2 := ((h1.const_mul (-w)).cexp).div_const w
  convert h2 using 1
  · funext s; push_cast; ring_nf
  · have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp

theorem tendsto_exp_neg_div_nhdsGT {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => Real.exp (-r / t)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => -r / t) (𝓝[>] 0) atBot := by
    have h1 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hr
    exact (tendsto_neg_atTop_atBot.comp h1).congr fun t => by
      simp [Function.comp, div_eq_mul_inv]
  exact Real.tendsto_exp_atBot.comp h

theorem tendsto_cexp_neg_div_nhdsGT {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun t : ℝ => cexp (-w / t)) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_exp_neg_div_nhdsGT hw).congr' ?_
  filter_upwards with t
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.div_ofReal_re, neg_div]

theorem integral_cexp_neg_div_div_sq {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => cexp (-w / t) / (t : ℂ) ^ 2) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), cexp (-w / t) / (t : ℂ) ^ 2 = 1 / w := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  set r := w.re
  let g : ℝ → ℝ := fun t => if t ≤ 0 then 0 else Real.exp (-r / t) / r
  have hgd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (Real.exp (-r / x) / x ^ 2) x := by
    intro x hx
    have hx' : x ≠ 0 := ne_of_gt hx
    have hc' : HasDerivAt (fun s : ℝ => Real.exp (-r / s) / r) (Real.exp (-r / x) / x ^ 2) x := by
      have h2 := (((hasDerivAt_inv hx').const_mul (-r)).exp).div_const r
      convert h2 using 1
      · funext s; simp [div_eq_mul_inv]
      · field_simp
    refine hc'.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hx] with s hs
    simp [g, not_le.2 hs]
  have hgc : ContinuousWithinAt g (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h0 : g 0 = 0 := by simp [g]
    rw [ContinuousWithinAt, h0]
    have := (tendsto_exp_neg_div_nhdsGT hw).div_const r
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [g, not_le.2 (show (0 : ℝ) < s from hs)]
  have hgt : Tendsto g atTop (𝓝 (1 / r)) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-r / t) / r) atTop (𝓝 (Real.exp (-r * 0) / r)) := by
      refine (Real.continuous_exp.continuousAt.tendsto.comp ?_).div_const r
      exact (tendsto_inv_atTop_zero.const_mul (-r)).congr fun t => by rw [div_eq_mul_inv]
    simp only [mul_zero, Real.exp_zero] at h1
    refine h1.congr' ?_
    filter_upwards [Ioi_mem_atTop 0] with s hs
    simp [g, not_le.2 (show (0 : ℝ) < s from hs)]
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-r / t) / t ^ 2) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg hgc hgd (fun x _ => by positivity) hgt
  have hcint : IntegrableOn (fun t : ℝ => cexp (-w / t) / (t : ℂ) ^ 2) (Ioi 0) := by
    refine hint.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun t : ℝ => cexp (-w / t) / (t : ℂ) ^ 2).aestronglyMeasurable
    · filter_upwards with t
      rw [norm_div, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      apply le_of_eq
      congr 2
      simp [Complex.div_ofReal_re, neg_div, r]
  refine ⟨hcint, ?_⟩
  let F : ℝ → ℂ := fun t => if t ≤ 0 then 0 else cexp (-w / t) / w
  have hFd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (cexp (-w / x) / (x : ℂ) ^ 2) x := by
    intro x hx
    refine (hasDerivAt_cexp_neg_div hw0 (ne_of_gt hx)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hx] with s hs
    simp [F, not_le.2 hs]
  have hFc : ContinuousWithinAt F (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h0 : F 0 = 0 := by simp [F]
    rw [ContinuousWithinAt, h0]
    have := (tendsto_cexp_neg_div_nhdsGT hw).div_const w
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [F, not_le.2 (show (0 : ℝ) < s from hs)]
  have hFt : Tendsto F atTop (𝓝 (1 / w)) := by
    have h1 : Tendsto (fun t : ℝ => cexp (-w * ((t⁻¹ : ℝ) : ℂ)) / w) atTop
        (𝓝 (cexp (-w * ((0 : ℝ) : ℂ)) / w)) := by
      refine (Complex.continuous_exp.continuousAt.tendsto.comp ?_).div_const w
      exact ((Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul (-w)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h1
    refine h1.congr' ?_
    filter_upwards [Ioi_mem_atTop 0] with s hs
    simp [F, not_le.2 (show (0 : ℝ) < s from hs), div_eq_mul_inv]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hFc hFd hcint hFt]
  simp [F]

theorem integral_exp_neg_div_div_sq {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-a / t) / t ^ 2 = 1 / a := by
  have h := (integral_cexp_neg_div_div_sq (w := (a : ℂ)) (by simpa using ha)).2
  have h' : ∫ t in Ioi (0 : ℝ), ((Real.exp (-a / t) / t ^ 2 : ℝ) : ℂ) = ((1 / a : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; rfl
  rw [integral_complex_ofReal] at h'
  exact_mod_cast h'

theorem integrableOn_cexp_mul_Ioi {a : ℂ} (ha : a.re < 0) :
    IntegrableOn (fun v : ℝ => cexp (a * v)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi ha 0

theorem integral_cexp_mul_Ioi {a : ℂ} (ha : a.re < 0) :
    ∫ v in Ioi (0 : ℝ), cexp (a * v) = -1 / a := by
  rw [integral_exp_mul_complex_Ioi ha 0]
  simp

theorem integral_cexp_mul_Iic {a : ℂ} (ha : 0 < a.re) :
    ∫ v in Iic (0 : ℝ), cexp (a * v) = 1 / a := by
  rw [integral_exp_mul_complex_Iic ha 0]
  simp

theorem integrable_and_integral_of_two_sided {f : ℝ → ℂ} {a b : ℂ} (ha : 0 < a.re)
    (hb : b.re < 0) (hfa : ∀ v ≤ 0, f v = cexp (a * v)) (hfb : ∀ v > 0, f v = cexp (b * v)) :
    Integrable f ∧ ∫ v, f v = 1 / a - 1 / b := by
  have h1 : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic ha 0).congr_fun (fun v hv => (hfa v hv).symm)
      measurableSet_Iic
  have h2 : IntegrableOn f (Ioi 0) :=
    (integrableOn_cexp_mul_Ioi hb).congr_fun (fun v hv => (hfb v hv).symm) measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · have := h1.union h2
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  · rw [← intervalIntegral.integral_Iic_add_Ioi h1 h2,
      setIntegral_congr_fun measurableSet_Iic (fun v hv => hfa v hv),
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => hfb v hv),
      integral_cexp_mul_Iic ha, integral_cexp_mul_Ioi hb]
    ring

noncomputable def twoSidedExp (β : ℂ) (v : ℝ) : ℂ := cexp (-β * |v|)

theorem integrable_twoSidedExp {β : ℂ} (hβ : 0 < β.re) : Integrable (twoSidedExp β) :=
  (integrable_and_integral_of_two_sided (a := β) (b := -β) hβ (by simpa using hβ)
    (fun v hv => by simp [twoSidedExp, abs_of_nonpos hv])
    (fun v hv => by simp [twoSidedExp, abs_of_pos hv])).1

theorem continuous_twoSidedExp (β : ℂ) : Continuous (twoSidedExp β) := by
  unfold twoSidedExp; fun_prop

theorem fourier_twoSidedExp {β : ℂ} (hβ : 0 < β.re) (w : ℝ) :
    𝓕 (twoSidedExp β) w = 2 * β / (β ^ 2 + ((2 * Real.pi * w : ℝ) : ℂ) ^ 2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set s : ℂ := ((2 * Real.pi * w : ℝ) : ℂ) * I
  have h := integrable_and_integral_of_two_sided (f := fun v : ℝ =>
      cexp (↑(-2 * Real.pi * v * w) * I) • twoSidedExp β v) (a := β - s) (b := -β - s)
    (by simpa [s] using hβ) (by simpa [s] using hβ)
    (fun v hv => by
      simp only [twoSidedExp, abs_of_nonpos hv, smul_eq_mul, ← Complex.exp_add, s]
      congr 1; push_cast; ring)
    (fun v hv => by
      simp only [twoSidedExp, abs_of_pos hv, smul_eq_mul, ← Complex.exp_add, s]
      congr 1; push_cast; ring)
  rw [h.2]
  have h1 : β - s ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith
  have h2 : -β - s ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith
  have h3 : β ^ 2 + ((2 * Real.pi * w : ℝ) : ℂ) ^ 2 = (β - s) * (β + s) := by
    simp only [s]; ring_nf; rw [I_sq]; ring
  have h4 : β + s ≠ 0 := by
    intro h0; apply h2; linear_combination -h0
  rw [h3]
  field_simp
  ring

theorem norm_sq_add_sq_ge (β : ℂ) (y : ℝ) :
    min (β ^ 2).re 1 * (1 + y ^ 2) ≤ ‖β ^ 2 + (y : ℂ) ^ 2‖ := by
  have hre : (β ^ 2 + (y : ℂ) ^ 2).re = (β ^ 2).re + y ^ 2 := by
    simp [← Complex.ofReal_pow]
  calc min (β ^ 2).re 1 * (1 + y ^ 2) = min (β ^ 2).re 1 + min (β ^ 2).re 1 * y ^ 2 := by ring
    _ ≤ (β ^ 2).re + y ^ 2 := by
        gcongr
        · exact min_le_left _ _
        · calc min (β ^ 2).re 1 * y ^ 2 ≤ 1 * y ^ 2 := by
                gcongr; exact min_le_right _ _
            _ = y ^ 2 := one_mul _
    _ = (β ^ 2 + (y : ℂ) ^ 2).re := hre.symm
    _ ≤ ‖β ^ 2 + (y : ℂ) ^ 2‖ := Complex.re_le_norm _

theorem sq_add_sq_ne_zero {β : ℂ} (hβ2 : 0 < (β ^ 2).re) (y : ℝ) : β ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
  intro h
  have := norm_sq_add_sq_ge β y
  rw [h, norm_zero] at this
  have : 0 < min (β ^ 2).re 1 * (1 + y ^ 2) := by
    have : 0 < min (β ^ 2).re 1 := lt_min hβ2 one_pos
    positivity
  linarith

theorem integrable_div_sq_add_sq {β : ℂ} (hβ2 : 0 < (β ^ 2).re) (C : ℂ) {g : ℝ → ℂ}
    (hg : Continuous g) (hgn : ∀ y, ‖g y‖ ≤ 1) :
    Integrable (fun y : ℝ => g y * (C / (β ^ 2 + (y : ℂ) ^ 2))) := by
  set m := min (β ^ 2).re 1
  have hm : 0 < m := lt_min hβ2 one_pos
  refine (integrable_inv_one_add_sq.const_mul (‖C‖ / m)).mono' ?_ ?_
  · refine (hg.mul ?_).aestronglyMeasurable
    exact continuous_const.div (by fun_prop) (sq_add_sq_ne_zero hβ2)
  · filter_upwards with y
    have hpos : 0 < m * (1 + y ^ 2) := by positivity
    rw [norm_mul, norm_div]
    calc ‖g y‖ * (‖C‖ / ‖β ^ 2 + (y : ℂ) ^ 2‖) ≤ 1 * (‖C‖ / (m * (1 + y ^ 2))) := by
          gcongr
          · exact hgn y
          · exact norm_sq_add_sq_ge β y
      _ = ‖C‖ / m * (1 + y ^ 2)⁻¹ := by field_simp

theorem integral_cexp_mul_I_div_sq_add_sq {β : ℂ} (hβ : 0 < β.re) (hβ2 : 0 < (β ^ 2).re)
    (x : ℝ) :
    ∫ y : ℝ, cexp (↑(y * x) * I) * (1 / (β ^ 2 + (y : ℂ) ^ 2)) =
      Real.pi / β * cexp (-β * |x|) := by
  have hβ0 : β ≠ 0 := by intro h; simp [h] at hβ
  have hF : 𝓕 (twoSidedExp β) = fun w : ℝ => 2 * β / (β ^ 2 + ((2 * Real.pi * w : ℝ) : ℂ) ^ 2) :=
    funext (fourier_twoSidedExp hβ)
  have hFint : Integrable (𝓕 (twoSidedExp β)) := by
    rw [hF]
    have := (integrable_div_sq_add_sq hβ2 (2 * β) (g := fun _ => 1) continuous_const
      (fun _ => by simp)).comp_mul_left' (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    simpa using this
  have hinv := (integrable_twoSidedExp hβ).fourierInv_fourier_eq hFint
    (continuous_twoSidedExp β).continuousAt (v := x)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hF] at hinv
  set g : ℝ → ℂ := fun y => cexp (↑(y * x) * I) * (2 * β / (β ^ 2 + (y : ℂ) ^ 2))
  have hg : ∫ w : ℝ, g (2 * Real.pi * w) = twoSidedExp β x := by
    rw [← hinv]
    congr 1; funext w
    simp only [g, smul_eq_mul]
    congr 2
    push_cast; ring
  rw [Measure.integral_comp_mul_left g (2 * Real.pi)] at hg
  set J := ∫ y : ℝ, cexp (↑(y * x) * I) * (1 / (β ^ 2 + (y : ℂ) ^ 2)) with hJ
  have hgi : ∫ y, g y = 2 * β * J := by
    rw [hJ, ← integral_const_mul]
    congr 1; funext y
    simp only [g]; ring
  rw [hgi] at hg
  clear_value J
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_of_pos (inv_pos.2 hpi), Complex.real_smul] at hg
  simp only [twoSidedExp] at hg
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← hg]
  push_cast
  field_simp

theorem exp_neg_sq_mul_eq_integral {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ((Real.exp (-c ^ 2 * t) : ℝ) : ℂ) = ((Real.sqrt (Real.pi * t))⁻¹ : ℝ) *
      ∫ y : ℝ, cexp (I * ((2 * c : ℝ) : ℂ) * y) * cexp (-(t : ℂ)⁻¹ * (y : ℂ) ^ 2) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hb : 0 < ((t : ℂ)⁻¹).re := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]; positivity
  rw [fourierIntegral_gaussian hb]
  have h1 : (Real.pi : ℂ) / (t : ℂ)⁻¹ = ((Real.pi * t : ℝ) : ℂ) := by
    push_cast; field_simp
  have h2 : ((Real.pi * t : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi * t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  have hs : Real.sqrt (Real.pi * t) ≠ 0 := by positivity
  rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hs, Complex.ofReal_one, one_mul,
    Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring

theorem integral_laplace_levy_kernel {β : ℂ} (hβ : 0 < β.re) (hβ2 : 0 < (β ^ 2).re) {c : ℝ}
    (hc : 0 ≤ c) :
    ∫ t in Ioi (0 : ℝ), β * cexp (-β ^ 2 / t) *
        ((Real.exp (-c ^ 2 * t) / (t * Real.sqrt t) : ℝ) : ℂ) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * cexp (-2 * c * β) := by
  have hβ0 : β ≠ 0 := by intro h; simp [h] at hβ
  set r := (β ^ 2).re
  let F : ℝ → ℝ → ℂ := fun t y =>
    β * cexp (I * ((2 * c : ℝ) : ℂ) * y) * (cexp (-(β ^ 2 + (y : ℂ) ^ 2) / t) / (t : ℂ) ^ 2)
  have hw : ∀ y : ℝ, 0 < (β ^ 2 + (y : ℂ) ^ 2).re := by
    intro y; simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re]; positivity
  have hsqπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), β * cexp (-β ^ 2 / t) *
      ((Real.exp (-c ^ 2 * t) / (t * Real.sqrt t) : ℝ) : ℂ) =
      ((Real.sqrt Real.pi)⁻¹ : ℝ) * ∫ y : ℝ, F t y := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hst : Real.sqrt t ≠ 0 := by positivity
    have hstC : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hst
    have hsπC : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqπ
    have hF : ∀ y : ℝ, F t y = (β * cexp (-β ^ 2 / t) / (t : ℂ) ^ 2) *
        (cexp (I * ((2 * c : ℝ) : ℂ) * y) * cexp (-(t : ℂ)⁻¹ * (y : ℂ) ^ 2)) := by
      intro y
      simp only [F]
      have : cexp (-(β ^ 2 + (y : ℂ) ^ 2) / t) =
          cexp (-β ^ 2 / t) * cexp (-(t : ℂ)⁻¹ * (y : ℂ) ^ 2) := by
        rw [← Complex.exp_add]; congr 1; field_simp; ring
      rw [this]; field_simp
    simp_rw [hF]
    rw [integral_const_mul, Complex.ofReal_div, exp_neg_sq_mul_eq_integral ht c]
    have hsq : Real.sqrt (Real.pi * t) = Real.sqrt Real.pi * Real.sqrt t :=
      Real.sqrt_mul Real.pi_pos.le t
    have htt : ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) = t := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
    rw [hsq]
    push_cast
    field_simp
    rw [show ((Real.sqrt t : ℝ) : ℂ) ^ 2 = t by rw [sq, htt]]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [F, Function.uncurry_def]
    fun_prop
  have hnorm : ∀ t y : ℝ, ‖F t y‖ = ‖β‖ * (Real.exp (-(r + y ^ 2) / t) / t ^ 2) := by
    intro t y
    simp only [F, norm_mul, norm_div, Complex.norm_exp, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have h1 : (I * ((2 * c : ℝ) : ℂ) * (y : ℂ)).re = 0 := by simp
    have h2 : (-(β ^ 2 + (y : ℂ) ^ 2) / (t : ℂ)).re = -(r + y ^ 2) / t := by
      rw [Complex.div_ofReal_re]
      simp [r, ← Complex.ofReal_pow]
    rw [h1, h2, Real.exp_zero, mul_one]
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · change Integrable (fun t => F t y) (volume.restrict (Ioi 0))
      exact (integral_cexp_neg_div_div_sq (hw y)).1.const_mul
        (β * cexp (I * ((2 * c : ℝ) : ℂ) * y))
    · have hval : ∀ y : ℝ, ∫ t in Ioi (0 : ℝ), ‖F t y‖ = ‖β‖ * (r + y ^ 2)⁻¹ := by
        intro y
        simp_rw [hnorm]
        rw [integral_const_mul, integral_exp_neg_div_div_sq (by positivity), one_div]
      change Integrable (fun y : ℝ => ∫ t in Ioi (0 : ℝ), ‖F t y‖) volume
      simp_rw [hval]
      set m := min r 1
      have hm : 0 < m := lt_min hβ2 one_pos
      refine (integrable_inv_one_add_sq.const_mul (‖β‖ / m)).mono' ?_ ?_
      · exact (Continuous.aestronglyMeasurable (by
          refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y => ?_)
          positivity))
      · filter_upwards with y
        have h1 : m * (1 + y ^ 2) ≤ r + y ^ 2 := by
          have := min_le_left r 1
          have := min_le_right r 1
          nlinarith [sq_nonneg y]
        have hpos : 0 < m * (1 + y ^ 2) := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc ‖β‖ * (r + y ^ 2)⁻¹ ≤ ‖β‖ * (m * (1 + y ^ 2))⁻¹ := by
              gcongr
          _ = ‖β‖ / m * (1 + y ^ 2)⁻¹ := by field_simp
  rw [integral_integral_swap hint]
  have hinner : ∀ y : ℝ, ∫ t in Ioi (0 : ℝ), F t y =
      β * (cexp (↑(y * (2 * c)) * I) * (1 / (β ^ 2 + (y : ℂ) ^ 2))) := by
    intro y
    simp only [F]
    rw [integral_const_mul, (integral_cexp_neg_div_div_sq (hw y)).2]
    have : cexp (I * ((2 * c : ℝ) : ℂ) * y) = cexp (↑(y * (2 * c)) * I) := by
      congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_cexp_mul_I_div_sq_add_sq hβ hβ2,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)]
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) = Real.pi := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hsπC : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqπ
  push_cast
  field_simp
  rw [← hπ]
  ring_nf

noncomputable def nullBeta : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * (2 + ((Real.pi / 2 : ℝ) : ℂ) * I)

theorem nullBeta_sq :
    nullBeta ^ 2 = ((8 - Real.pi ^ 2 / 2 : ℝ) : ℂ) + ((4 * Real.pi : ℝ) : ℂ) * I := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [nullBeta, mul_pow, h2]
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem nullBeta_re : nullBeta.re = 2 * Real.sqrt 2 := by
  simp [nullBeta]; ring

theorem nullBeta_im : nullBeta.im = Real.sqrt 2 * (Real.pi / 2) := by
  simp [nullBeta]

theorem nullBeta_re_pos : 0 < nullBeta.re := by
  rw [nullBeta_re]; positivity

theorem nullBeta_sq_re : (nullBeta ^ 2).re = 8 - Real.pi ^ 2 / 2 := by
  rw [nullBeta_sq, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re]
  ring

theorem nullBeta_sq_re_pos : 0 < (nullBeta ^ 2).re := by
  rw [nullBeta_sq_re]
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

noncomputable def laplaceNullFunction (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
    (nullBeta * cexp (-nullBeta ^ 2 / t)).re * (Real.exp (-t / 8) / (t * Real.sqrt t))

theorem exp_neg_div_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Real.exp (-r / t) ≤ 6 * t ^ 3 / r ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (r / t) (by positivity) 3
  have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h
  rw [neg_div, Real.exp_neg]
  have hpos : 0 < (r / t) ^ 3 / 6 := by positivity
  calc (Real.exp (r / t))⁻¹ ≤ ((r / t) ^ 3 / 6)⁻¹ := by gcongr
    _ = 6 * t ^ 3 / r ^ 3 := by field_simp

theorem abs_laplaceNullFunction_le {t : ℝ} (ht : 0 < t) :
    |laplaceNullFunction t| ≤
      ‖nullBeta‖ * (Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t)) := by
  have hst : 0 < t * Real.sqrt t := by positivity
  simp only [laplaceNullFunction, not_le.2 ht, ite_false, abs_mul]
  have h1 : |(nullBeta * cexp (-nullBeta ^ 2 / t)).re| ≤
      ‖nullBeta‖ * Real.exp (-(nullBeta ^ 2).re / t) := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_exp, Complex.div_ofReal_re, Complex.neg_re]
  have h2 : |Real.exp (-t / 8) / (t * Real.sqrt t)| ≤ 1 / (t * Real.sqrt t) := by
    rw [abs_of_nonneg (by positivity)]
    gcongr
    rw [Real.exp_le_one_iff]; linarith
  calc |(nullBeta * cexp (-nullBeta ^ 2 / t)).re| * |Real.exp (-t / 8) / (t * Real.sqrt t)|
      ≤ (‖nullBeta‖ * Real.exp (-(nullBeta ^ 2).re / t)) * (1 / (t * Real.sqrt t)) := by
        gcongr
    _ = _ := by ring

theorem abs_laplaceNullFunction_le_mul (t : ℝ) :
    |laplaceNullFunction t| ≤
      6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (|t| * Real.sqrt |t|) := by
  have hr := nullBeta_sq_re_pos
  rcases le_or_gt t 0 with ht | ht
  · simp only [laplaceNullFunction, ht, ite_true, abs_zero]; positivity
  · refine (abs_laplaceNullFunction_le ht).trans ?_
    rw [abs_of_pos ht]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have he := exp_neg_div_le hr ht
    calc ‖nullBeta‖ * (Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t))
        ≤ ‖nullBeta‖ * (6 * t ^ 3 / (nullBeta ^ 2).re ^ 3 / (t * Real.sqrt t)) := by gcongr
      _ = 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (t * Real.sqrt t) := by
        field_simp
        have h2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
        have h3 := mul_le_mul_of_nonneg_left (le_of_eq h2) (norm_nonneg nullBeta)
        have h4 := mul_le_mul_of_nonneg_left (le_of_eq h2.symm) (norm_nonneg nullBeta)
        nlinarith [h3, h4, norm_nonneg nullBeta]

theorem continuous_laplaceNullFunction : Continuous laplaceNullFunction := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [gt_mem_nhds ht] with s hs
    simp [laplaceNullFunction, hs.le]
  · have h0 : laplaceNullFunction 0 = 0 := by simp [laplaceNullFunction]
    rw [ContinuousAt, h0]
    have hb : Tendsto (fun s : ℝ => 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 * (|s| * Real.sqrt |s|))
        (𝓝 0) (𝓝 0) := by
      have : Continuous (fun s : ℝ => 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3 *
          (|s| * Real.sqrt |s|)) := by fun_prop
      simpa using this.tendsto 0
    exact squeeze_zero_norm (fun s => by
      rw [Real.norm_eq_abs]; exact abs_laplaceNullFunction_le_mul s) hb
  · have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hst : t * Real.sqrt t ≠ 0 := by positivity
    have hc : ContinuousAt (fun s : ℝ => (nullBeta * cexp (-nullBeta ^ 2 / s)).re *
        (Real.exp (-s / 8) / (s * Real.sqrt s))) t := by
      refine ContinuousAt.mul ?_ ?_
      · refine Complex.continuous_re.continuousAt.comp ?_
        refine continuousAt_const.mul (Complex.continuous_exp.continuousAt.comp ?_)
        exact continuousAt_const.div Complex.continuous_ofReal.continuousAt htC
      · refine ContinuousAt.div (by fun_prop) (by fun_prop) hst
    refine hc.congr ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    simp [laplaceNullFunction, not_le.2 hs]

theorem bounded_laplaceNullFunction : ∃ B : ℝ, ∀ t, |laplaceNullFunction t| ≤ B := by
  set K := 6 * ‖nullBeta‖ / (nullBeta ^ 2).re ^ 3
  have hK : 0 ≤ K := by have := nullBeta_sq_re_pos; positivity
  have hβn : 0 ≤ ‖nullBeta‖ := norm_nonneg _
  refine ⟨‖nullBeta‖ + K, fun t => ?_⟩
  rcases le_or_gt t 0 with h0 | h0
  · simp only [laplaceNullFunction, h0, ite_true, abs_zero]; positivity
  rcases le_or_gt t 1 with ht | ht
  · refine (abs_laplaceNullFunction_le_mul t).trans ?_
    have h1 : |t| * Real.sqrt |t| ≤ 1 := by
      rw [abs_of_pos h0]
      have : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht
      nlinarith [Real.sqrt_nonneg t]
    nlinarith
  · refine (abs_laplaceNullFunction_le h0).trans ?_
    have hs1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht.le
    have he : Real.exp (-(nullBeta ^ 2).re / t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := nullBeta_sq_re_pos
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
    have h2 : Real.exp (-(nullBeta ^ 2).re / t) / (t * Real.sqrt t) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    nlinarith

theorem laplaceNullFunction_two_ne_zero : laplaceNullFunction 2 ≠ 0 := by
  have he : cexp (-nullBeta ^ 2 / ((2 : ℝ) : ℂ)) = ((Real.exp (Real.pi ^ 2 / 4 - 4) : ℝ) : ℂ) := by
    have : -nullBeta ^ 2 / ((2 : ℝ) : ℂ) =
        ((Real.pi ^ 2 / 4 - 4 : ℝ) : ℂ) + ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) := by
      rw [nullBeta_sq]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.ofReal_exp]
  simp only [laplaceNullFunction, show ¬ (2 : ℝ) ≤ 0 by norm_num, ite_false]
  rw [he, Complex.re_mul_ofReal, nullBeta_re]
  have : 0 < Real.sqrt 2 := by positivity
  have : 0 < 2 * Real.sqrt 2 * Real.exp (Real.pi ^ 2 / 4 - 4) *
      (Real.exp (-2 / 8) / (2 * Real.sqrt 2)) := by positivity
  exact this.ne'

theorem exists_Ioo_laplaceNullFunction_ne_zero :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Ioo s t, laplaceNullFunction u ≠ 0 := by
  have hopen : IsOpen {u : ℝ | laplaceNullFunction u ≠ 0} :=
    isOpen_ne_fun continuous_laplaceNullFunction continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 2 laplaceNullFunction_two_ne_zero
  set δ := min ε 1
  have hδ : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  refine ⟨2 - δ, 2 + δ, by linarith, by linarith, fun u hu => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hu.1, hu.2]

theorem integral_exp_mul_laplaceNullFunction (k : ℕ) (hk : 1 ≤ k) :
    ∫ τ in Ioi (0 : ℝ), Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / 2 * τ)) * laplaceNullFunction τ =
      0 := by
  set c : ℝ := (2 * (k : ℝ) - 1) / (2 * Real.sqrt 2)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 ≤ c := by
    have : 0 ≤ 2 * (k : ℝ) - 1 := by linarith
    positivity
  have hc2 : c ^ 2 = (k : ℝ) * ((k : ℝ) - 1) / 2 + 1 / 8 := by
    simp only [c, div_pow, mul_pow, hs2sq]; ring
  have hcs : c * Real.sqrt 2 = (2 * (k : ℝ) - 1) / 2 := by
    simp only [c]; field_simp
  have hmain := integral_laplace_levy_kernel nullBeta_re_pos nullBeta_sq_re_pos hc
  have hne : ((Real.sqrt Real.pi : ℝ) : ℂ) * cexp (-2 * c * nullBeta) ≠ 0 := by
    have : Real.sqrt Real.pi ≠ 0 := by positivity
    exact mul_ne_zero (by exact_mod_cast this) (Complex.exp_ne_zero _)
  have hint : IntegrableOn (fun t : ℝ => nullBeta * cexp (-nullBeta ^ 2 / t) *
      ((Real.exp (-c ^ 2 * t) / (t * Real.sqrt t) : ℝ) : ℂ)) (Ioi 0) := by
    by_contra h
    rw [integral_undef h] at hmain
    exact hne hmain.symm
  have hpt : ∀ τ ∈ Ioi (0 : ℝ),
      Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / 2 * τ)) * laplaceNullFunction τ =
      (nullBeta * cexp (-nullBeta ^ 2 / τ) *
        ((Real.exp (-c ^ 2 * τ) / (τ * Real.sqrt τ) : ℝ) : ℂ)).re := by
    intro τ hτ
    have hτ : (0 : ℝ) < τ := hτ
    simp only [laplaceNullFunction, not_le.2 hτ, ite_false, Complex.re_mul_ofReal]
    rw [hc2]
    have : Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / 2 + 1 / 8) * τ) =
        Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / 2 * τ)) * Real.exp (-τ / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have hre : ∫ τ in Ioi (0 : ℝ), (nullBeta * cexp (-nullBeta ^ 2 / τ) *
        ((Real.exp (-c ^ 2 * τ) / (τ * Real.sqrt τ) : ℝ) : ℂ)).re =
      (∫ τ in Ioi (0 : ℝ), nullBeta * cexp (-nullBeta ^ 2 / τ) *
        ((Real.exp (-c ^ 2 * τ) / (τ * Real.sqrt τ) : ℝ) : ℂ)).re := integral_re hint
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hre, hmain,
    Complex.re_ofReal_mul, Complex.exp_re]
  have him : (-2 * c * nullBeta).im = -((2 * ((k : ℝ) - 1) + 1) * Real.pi / 2) := by
    have : (-2 * c * nullBeta).im = -2 * c * nullBeta.im := by simp
    rw [this, nullBeta_im]
    have h2 : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ hs2.ne'
    linear_combination (-Real.pi / 2) * hcs + (-(k : ℝ) * Real.pi / 2 + Real.pi / 4) * h2
  rw [him, Real.cos_neg, Real.cos_eq_zero_iff.2 ⟨(k : ℤ) - 1, by push_cast; ring⟩]
  ring

end Rhone.Analysis
