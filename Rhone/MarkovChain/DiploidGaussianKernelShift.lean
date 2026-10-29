/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianIncrementLaw
public import Mathlib.Probability.Moments.Variance
/-! # Bounded Lipschitz comparison of Gaussian increments with target redraw -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private theorem integral_abs_le_root_second (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    (∫ x, |x| ∂μ) ≤ Real.sqrt (∫ x, x ^ 2 ∂μ) := by
  have hm : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2
  have hv := variance_nonneg (fun x : ℝ => ‖x‖) μ
  rw [variance_eq_sub hm.norm] at hv
  simp only [Pi.pow_apply, Real.norm_eq_abs, sq_abs] at hv
  exact (Real.le_sqrt (integral_nonneg (fun x => abs_nonneg x))
    (integral_nonneg (fun x => sq_nonneg x))).mpr (by linarith)

theorem gaussian_increment_redraw_test_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f)
    (hfbound : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    |(∫ z, f z ∂(μ.prod (gaussianReal 0 T)).map (fun p => p.1+p.2)) -
      (∫ z, f z ∂gaussianReal 0 T)| ≤ (K : ℝ)*Real.sqrt (∫ x, x ^ 2 ∂μ) := by
  have hT0 := le_of_lt hT
  obtain ⟨C, hC⟩ := hfbound
  have hfm : Measurable f := hf.continuous.measurable
  have hi (ν : Measure ℝ) [IsProbabilityMeasure ν] : Integrable f ν := by
    apply Integrable.of_bound hfm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hsum : Measurable (fun p : ℝ × ℝ => p.1+p.2) := by fun_prop
  have hp : Integrable (fun p : ℝ × ℝ => f (p.1+p.2)) (μ.prod (gaussianReal 0 T)) := by
    apply Integrable.of_bound (hfm.comp hsum).aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs] using hC (p.1+p.2))
  have hg := (hi (gaussianReal 0 T)).comp_snd μ
  have hm : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2
  have hab := hm.norm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hb : Integrable (fun p : ℝ × ℝ => (K : ℝ)*|p.1|) (μ.prod (gaussianReal 0 T)) :=
    (hab.comp_fst _).const_mul (K : ℝ)
  rw [integral_map hsum.aemeasurable hfm.aestronglyMeasurable]
  have he : (∫ p : ℝ × ℝ, f p.2 ∂μ.prod (gaussianReal 0 T)) =
      ∫ z, f z ∂gaussianReal 0 T := by
    simpa using integral_fun_snd (fun z : ℝ => f z) (μ := μ) (ν := gaussianReal 0 T)
  rw [← he, ← integral_sub hp hg]
  calc
    _ ≤ ∫ p, |f (p.1+p.2)-f p.2| ∂μ.prod (gaussianReal 0 T) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p, (K : ℝ)*|p.1| ∂μ.prod (gaussianReal 0 T) := by
      apply integral_mono (hp.sub hg).abs hb
      intro p
      simpa only [Pi.sub_apply, Real.dist_eq, add_sub_cancel_right] using
        hf.dist_le_mul (p.1+p.2) p.2
    _ = (K : ℝ)*(∫ x, |x| ∂μ) := by
      rw [integral_const_mul, integral_fun_fst]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_root_second μ h2) K.property

theorem gaussian_increment_redraw_scaled_test_error
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f)
    (hfbound : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    |(∫ z, f (z/Real.sqrt (T : ℝ))
        ∂(μ.prod (gaussianReal 0 T)).map (fun p => p.1+p.2)) -
      (∫ z, f (z/Real.sqrt (T : ℝ)) ∂gaussianReal 0 T)| ≤
      (K : ℝ)*Real.sqrt ((∫ x, x ^ 2 ∂μ)/(T : ℝ)) := by
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hl : LipschitzWith (K/NNReal.sqrt T) (fun z => f (z/Real.sqrt (T : ℝ))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := hf.dist_le_mul (x/Real.sqrt (T : ℝ)) (y/Real.sqrt (T : ℝ))
    simpa only [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hs,
      NNReal.coe_div, Real.coe_sqrt, div_mul_eq_mul_div, mul_div_assoc] using he
  have hb : ∃ C : ℝ, ∀ x, |f (x/Real.sqrt (T : ℝ))| ≤ C := by
    obtain ⟨C, hC⟩ := hfbound
    exact ⟨C, fun x => hC _⟩
  have he := gaussian_increment_redraw_test_error μ h2 T hT _ _ hl hb
  apply he.trans_eq
  rw [NNReal.coe_div, Real.coe_sqrt,
    Real.sqrt_div (integral_nonneg (fun x => sq_nonneg x))]
  ring

end Rhone.MarkovChain.DiploidMarginalSelection
