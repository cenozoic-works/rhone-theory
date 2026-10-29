/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeFixedPositionTwoSampleLaw

/-! # Two samples: the stationary occupation measure of the SMC′ chain -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Set IntervalProcess
open scoped ENNReal

theorem lintegral_Ioi_exp_neg_comp_div {r : ℝ} (hr : 0 < r) (G : ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) * G (e / r) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) * G t := by
  have hw : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(r * t))) * G t :=
    Measurable.mul (by fun_prop) hG
  let K : ℝ → ℝ≥0∞ :=
    (Ioi 0).indicator fun t => ENNReal.ofReal (Real.exp (-(r * t))) * G t
  have hK : Measurable K := hw.indicator measurableSet_Ioi
  have h1 : ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) * G (e / r) =
      ∫⁻ e, K (r⁻¹ * e) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun e => ?_
    have hiff : e ∈ Ioi (0 : ℝ) ↔ r⁻¹ * e ∈ Ioi (0 : ℝ) := by
      simp only [mem_Ioi]
      constructor
      · intro he
        exact mul_pos (inv_pos.mpr hr) he
      · intro he
        by_contra hc
        exact absurd he (not_lt.mpr
          (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hr).le (not_lt.mp hc)))
    have harg : r * (r⁻¹ * e) = e := by
      field_simp
    by_cases he : e ∈ Ioi (0 : ℝ)
    · simp only [K]
      rw [indicator_of_mem he, indicator_of_mem (hiff.mp he), harg, inv_mul_eq_div]
    · simp only [K]
      rw [indicator_of_notMem he, indicator_of_notMem (fun hc => he (hiff.mpr hc))]
  have hmap := Real.map_volume_mul_left (a := r⁻¹) (inv_pos.mpr hr).ne'
  have h3 : ∫⁻ e, K (r⁻¹ * e) =
      ∫⁻ y, K y ∂(Measure.map (fun x : ℝ => r⁻¹ * x) volume) := by
    rw [lintegral_map hK (measurable_const_mul _)]
  rw [h1, h3, hmap, lintegral_smul_measure, lintegral_indicator measurableSet_Ioi, inv_inv,
    abs_of_pos hr, smul_eq_mul, ← lintegral_const_mul _ hw]
  refine lintegral_congr fun t => ?_
  rw [ENNReal.ofReal_mul hr.le, mul_assoc]

theorem setLIntegral_Ioi_comp_add (φ : ℝ → ℝ≥0∞) (p : ℝ) :
    ∫⁻ t in Ioi 0, φ (p + t) = ∫⁻ q in Ioi p, φ q := by
  have h := setLIntegral_Ici_comp_add φ 0 p
  rw [zero_add] at h
  calc ∫⁻ t in Ioi 0, φ (p + t) = ∫⁻ t in Ici 0, φ (p + t) :=
        setLIntegral_congr Ioi_ae_eq_Ici
    _ = ∫⁻ t in Ici 0, φ (t + p) := by
        refine lintegral_congr fun t => ?_
        rw [add_comm]
    _ = ∫⁻ q in Ici p, φ q := h
    _ = ∫⁻ q in Ioi p, φ q := setLIntegral_congr Ioi_ae_eq_Ici.symm

theorem lintegral_Ioo_rate_exp {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    ∫⁻ p in Ioo 0 q, ENNReal.ofReal (r * Real.exp (-(r * (q - p)))) =
      ENNReal.ofReal (1 - Real.exp (-(r * q))) := by
  have hF : ∀ p : ℝ, HasDerivAt (fun p : ℝ => Real.exp (r * p + -(r * q)))
      (r * Real.exp (r * p + -(r * q))) p := fun p => hasDerivAt_exp_affine r (-(r * q)) p
  have hf : Continuous fun p : ℝ => r * Real.exp (r * p + -(r * q)) := by fun_prop
  have h := lintegral_Ioo_ofReal_of_hasDerivAt hq hF hf
    (fun p _ => mul_nonneg hr (Real.exp_nonneg _))
  have harg : ∀ p : ℝ, -(r * (q - p)) = r * p + -(r * q) := fun p => by ring
  simp only [harg]
  rw [h]
  congr 1
  rw [show r * q + -(r * q) = 0 by ring, Real.exp_zero, mul_zero, zero_add]

theorem renewal_identity {r : ℝ} (hr : 0 < r) (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) * ψ t) +
        ∫⁻ p in Ioi 0, ENNReal.ofReal r *
          ∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) * ψ (p + t) =
      ENNReal.ofReal r * ∫⁻ q in Ioi 0, ψ q := by
  let g : ℝ × ℝ → ℝ≥0∞ := fun z =>
    if z.1 < z.2 then ENNReal.ofReal (r * Real.exp (-(r * (z.2 - z.1)))) * ψ z.2 else 0
  have hg : Measurable g := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
    exact Measurable.mul (by fun_prop) (hψ.comp measurable_snd)
  have hinner : ∀ p ∈ Ioi (0 : ℝ),
      ∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) * ψ (p + t) =
        ∫⁻ q in Ioi 0, g (p, q) := by
    intro p hp
    have h1 := setLIntegral_Ioi_comp_add
      (fun q => ENNReal.ofReal (r * Real.exp (-(r * (q - p)))) * ψ q) p
    simp only [add_sub_cancel_left] at h1
    rw [h1]
    have h2 : ∀ q : ℝ, g (p, q) = (Ioi p).indicator
        (fun q => ENNReal.ofReal (r * Real.exp (-(r * (q - p)))) * ψ q) q := by
      intro q
      by_cases hq : p < q
      · rw [indicator_of_mem (show q ∈ Ioi p from hq)]
        simp only [g, hq, ↓reduceIte]
      · rw [indicator_of_notMem (show q ∉ Ioi p from hq)]
        simp only [g, hq, ↓reduceIte]
    rw [lintegral_congr h2, lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi,
      sup_eq_left.mpr (mem_Ioi.mp hp).le]
  have hswap : ∫⁻ p in Ioi 0, ∫⁻ q in Ioi 0, g (p, q) =
      ∫⁻ q in Ioi 0, ∫⁻ p in Ioi 0, g (p, q) :=
    lintegral_lintegral_swap hg.aemeasurable
  have houter : ∀ q ∈ Ioi (0 : ℝ), ∫⁻ p in Ioi 0, g (p, q) =
      ENNReal.ofReal (1 - Real.exp (-(r * q))) * ψ q := by
    intro q hq
    have h2 : ∀ p : ℝ, g (p, q) = (Iio q).indicator
        (fun p => ENNReal.ofReal (r * Real.exp (-(r * (q - p)))) * ψ q) p := by
      intro p
      by_cases hp : p < q
      · rw [indicator_of_mem (show p ∈ Iio q from hp)]
        simp only [g, hp, ↓reduceIte]
      · rw [indicator_of_notMem (show p ∉ Iio q from hp)]
        simp only [g, hp, ↓reduceIte]
    rw [lintegral_congr h2, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio,
      lintegral_mul_const _ (by fun_prop), lintegral_Ioo_rate_exp hr.le (mem_Ioi.mp hq).le]
  have hsecond : ∫⁻ p in Ioi 0, ENNReal.ofReal r *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) * ψ (p + t) =
      ∫⁻ q in Ioi 0, ENNReal.ofReal r * (ENNReal.ofReal (1 - Real.exp (-(r * q))) * ψ q) := by
    have h1 : ∀ p ∈ Ioi (0 : ℝ), ENNReal.ofReal r *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (r * Real.exp (-(r * t))) * ψ (p + t) =
        ENNReal.ofReal r * ∫⁻ q in Ioi 0, g (p, q) := fun p hp => by
      rw [hinner p hp]
    rw [setLIntegral_congr_fun measurableSet_Ioi h1,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hswap,
      setLIntegral_congr_fun measurableSet_Ioi houter,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (r * Real.exp (-(r * t))) * ψ t :=
    Measurable.mul (by fun_prop) hψ
  rw [hsecond]
  refine (lintegral_add_left hm _).symm.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun q hq => ?_
  have he1 : Real.exp (-(r * q)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le (mem_Ioi.mp hq).le))
  have hsum : ENNReal.ofReal (Real.exp (-(r * q))) +
      ENNReal.ofReal (1 - Real.exp (-(r * q))) = 1 := by
    rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (sub_nonneg.mpr he1), add_sub_cancel,
      ENNReal.ofReal_one]
  rw [ENNReal.ofReal_mul hr.le]
  calc ENNReal.ofReal r * ENNReal.ofReal (Real.exp (-(r * q))) * ψ q +
        ENNReal.ofReal r * (ENNReal.ofReal (1 - Real.exp (-(r * q))) * ψ q)
      = ENNReal.ofReal r * ((ENNReal.ofReal (Real.exp (-(r * q))) +
          ENNReal.ofReal (1 - Real.exp (-(r * q)))) * ψ q) := by ring
    _ = ENNReal.ofReal r * ψ q := by rw [hsum, one_mul]

noncomputable def twoSampleHeightOp (f : ℝ → ℝ≥0∞) (h : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (twoSampleSelfMass h) * f h +
    ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a

theorem twoSampleHeightOp_zero (h : ℝ) : twoSampleHeightOp (fun _ => 0) h = 0 := by
  simp only [twoSampleHeightOp, mul_zero, lintegral_zero, add_zero]

theorem measurable_twoSampleHeightOp (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable fun z : ℝ × ℝ => twoSampleHeightOp (fun a => φ (z.1, a)) z.2 := by
  have hself : Measurable (fun h : ℝ => ENNReal.ofReal (twoSampleSelfMass h)) := by
    unfold twoSampleSelfMass
    fun_prop
  have hint : Measurable fun z : ℝ × ℝ =>
      ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity z.2 a) * φ (z.1, a) :=
    Measurable.lintegral_prod_right'
      (f := fun w : (ℝ × ℝ) × ℝ =>
        ENNReal.ofReal (twoSampleJumpDensity w.1.2 w.2) * φ (w.1.1, w.2))
      ((ENNReal.measurable_ofReal.comp (measurable_twoSampleJumpDensity.comp
        (measurable_fst.snd.prodMk measurable_snd))).mul
        (hφ.comp (measurable_fst.fst.prodMk measurable_snd)))
  exact ((hself.comp measurable_snd).mul hφ).add hint

noncomputable def twoSampleStepOp (R : ℝ) (φ : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (R * z.2 * Real.exp (-(R * z.2 * t))) *
    twoSampleHeightOp (fun a => φ (z.1 + t, a)) z.2

theorem measurable_twoSampleStepOp (R : ℝ) (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (twoSampleStepOp R φ) := by
  have h1 : Measurable fun w : (ℝ × ℝ) × ℝ =>
      twoSampleHeightOp (fun a => φ (w.1.1 + w.2, a)) w.1.2 :=
    (measurable_twoSampleHeightOp φ hφ).comp
      ((measurable_fst.fst.add measurable_snd).prodMk measurable_fst.snd)
  have h2 : Measurable fun w : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (R * w.1.2 * Real.exp (-(R * w.1.2 * w.2))) := by fun_prop
  exact Measurable.lintegral_prod_right' (h2.mul h1)

theorem twoSampleStepOp_eq_zero (R : ℝ) (φ : ℝ × ℝ → ℝ≥0∞)
    (hφ0 : ∀ q h : ℝ, 1 ≤ q → φ (q, h) = 0) {p : ℝ} (hp : 1 ≤ p) (h : ℝ) :
    twoSampleStepOp R φ (p, h) = 0 := by
  unfold twoSampleStepOp
  refine Eq.trans (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)
    fun t ht => ?_) lintegral_zero
  have hz : (fun a => φ (p + t, a)) = fun _ => 0 :=
    funext fun a => hφ0 _ a (hp.trans (le_add_of_nonneg_right (mem_Ioi.mp ht).le))
  dsimp only
  rw [hz, twoSampleHeightOp_zero, mul_zero]

theorem twoSampleOccupation_step {R : ℝ} (hR : 0 < R) (φ : ℝ × ℝ → ℝ≥0∞)
    (hφ : Measurable φ) :
    (∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * twoSampleStepOp R φ (0, h)) +
        ∫⁻ p in Ioi 0, ∫⁻ h in Ioi 0,
          ENNReal.ofReal (R * (h * Real.exp (-h))) * twoSampleStepOp R φ (p, h) =
      ∫⁻ q in Ioi 0, ∫⁻ h in Ioi 0, ENNReal.ofReal (R * (h * Real.exp (-h))) * φ (q, h) := by
  have hS := measurable_twoSampleStepOp R φ hφ
  have hκ := measurable_twoSampleHeightOp φ hφ
  have hw : Measurable fun h : ℝ => ENNReal.ofReal (R * (h * Real.exp (-h))) := by fun_prop
  have hwe : Measurable fun h : ℝ => ENNReal.ofReal (Real.exp (-h)) := by fun_prop
  have hswap1 : ∫⁻ p in Ioi 0, ∫⁻ h in Ioi 0,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * twoSampleStepOp R φ (p, h) =
      ∫⁻ h in Ioi 0, ∫⁻ p in Ioi 0,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * twoSampleStepOp R φ (p, h) := by
    refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
    exact (hw.comp measurable_snd).mul hS
  have hsplit : ∀ h ∈ Ioi (0 : ℝ), ∫⁻ p in Ioi 0,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * twoSampleStepOp R φ (p, h) =
      ENNReal.ofReal (Real.exp (-h)) *
        ∫⁻ p in Ioi 0, ENNReal.ofReal (R * h) * twoSampleStepOp R φ (p, h) := by
    intro h hh
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    rw [show R * (h * Real.exp (-h)) = Real.exp (-h) * (R * h) by ring,
      ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
  have hfirst : Measurable fun h : ℝ =>
      ENNReal.ofReal (Real.exp (-h)) * twoSampleStepOp R φ (0, h) :=
    hwe.mul (hS.comp (measurable_const.prodMk measurable_id))
  rw [hswap1, setLIntegral_congr_fun measurableSet_Ioi hsplit]
  refine (lintegral_add_left hfirst _).symm.trans ?_
  have hren : ∀ h ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-h)) * twoSampleStepOp R φ (0, h) +
        ENNReal.ofReal (Real.exp (-h)) *
          ∫⁻ p in Ioi 0, ENNReal.ofReal (R * h) * twoSampleStepOp R φ (p, h) =
      ∫⁻ q in Ioi 0, ENNReal.ofReal (R * (h * Real.exp (-h))) *
        twoSampleHeightOp (fun a => φ (q, a)) h := by
    intro h hh
    have hψ : Measurable fun q : ℝ => twoSampleHeightOp (fun a => φ (q, a)) h := by
      have h0 := hκ.comp (show Measurable fun q : ℝ => (q, h) from
        measurable_id.prodMk measurable_const)
      exact h0
    have hid := renewal_identity (mul_pos hR (mem_Ioi.mp hh)) _ hψ
    simp only [twoSampleStepOp, zero_add]
    rw [← mul_add, hid, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun q => ?_
    rw [show R * (h * Real.exp (-h)) = Real.exp (-h) * (R * h) by ring,
      ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioi hren]
  have hswap2 : ∫⁻ h in Ioi 0, ∫⁻ q in Ioi 0, ENNReal.ofReal (R * (h * Real.exp (-h))) *
        twoSampleHeightOp (fun a => φ (q, a)) h =
      ∫⁻ q in Ioi 0, ∫⁻ h in Ioi 0, ENNReal.ofReal (R * (h * Real.exp (-h))) *
        twoSampleHeightOp (fun a => φ (q, a)) h := by
    have hm2 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (R * (z.1 * Real.exp (-z.1))) *
        twoSampleHeightOp (fun a => φ (z.2, a)) z.1 := by
      have h0 := hκ.comp measurable_swap
      exact (hw.comp measurable_fst).mul h0
    exact lintegral_lintegral_swap hm2.aemeasurable
  rw [hswap2]
  refine lintegral_congr fun q => ?_
  have hinv := twoSample_lengthBiased_invariant (fun a => φ (q, a))
    (hφ.comp (measurable_const.prodMk measurable_id))
  have hpull : ∀ f : ℝ → ℝ≥0∞, ∫⁻ h in Ioi 0, ENNReal.ofReal (R * (h * Real.exp (-h))) * f h =
      ENNReal.ofReal R * ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) * f h := by
    intro f
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun h => ?_
    rw [ENNReal.ofReal_mul hR.le, mul_assoc]
  rw [hpull, hpull]
  congr 1

end Rhone.Coalescent.SmcPrime
