/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.NonnegativeLaplaceUniqueness
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Analytic.Uniqueness

/-! # Finite-measure Laplace uniqueness from one positive rectangle -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

private theorem analyticOnNhd_mgf_of_nonpos
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hneg : ∀ᵐ x ∂μ, X x ≤ 0) :
    AnalyticOnNhd ℝ (mgf X μ) (Ioi 0) := by
  have hsub : Ioi (0 : ℝ) ⊆ integrableExpSet X μ := by
    intro r hr
    change Integrable (fun x => Real.exp (r * X x)) μ
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards [hneg] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le hx)
  intro r hr
  exact analyticAt_mgf (interior_mono hsub (by simpa using hr))

theorem nonnegative_bivariate_laplace_unique_of_rectangle
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlap : ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
      (∫ x, Real.exp (-s * x.1) * Real.exp (-t * x.2) ∂μ) =
        ∫ x, Real.exp (-s * x.1) * Real.exp (-t * x.2) ∂ν) :
    μ = ν := by
  apply nonnegative_bivariate_laplace_unique μ ν hμ hν
  intro m n
  let X : ℝ × ℝ → ℝ := fun x => -((m : ℝ) * x.1 + (n : ℝ) * x.2)
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hXμ : ∀ᵐ x ∂μ, X x ≤ 0 := by
    filter_upwards [hμ] with x hx
    dsimp [X]
    exact neg_nonpos.mpr (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hx.1)
      (mul_nonneg (Nat.cast_nonneg _) hx.2))
  have hXν : ∀ᵐ x ∂ν, X x ≤ 0 := by
    filter_upwards [hν] with x hx
    dsimp [X]
    exact neg_nonpos.mpr (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hx.1)
      (mul_nonneg (Nat.cast_nonneg _) hx.2))
  have hμana := analyticOnNhd_mgf_of_nonpos μ X hX hXμ
  have hνana := analyticOnNhd_mgf_of_nonpos ν X hX hXν
  let d : ℝ := min a b / ((m : ℝ) + (n : ℝ) + 1)
  have hden : 0 < (m : ℝ) + (n : ℝ) + 1 := by positivity
  have hd : 0 < d := div_pos (lt_min ha hb) hden
  have hd_bound : d * ((m : ℝ) + (n : ℝ) + 1) = min a b := by
    dsimp [d]
    field_simp
  have heq (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) d) : mgf X μ r = mgf X ν r := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hma : r * (m : ℝ) ≤ a := by
      have hprod : r * ((m : ℝ) + (n : ℝ) + 1) < min a b := by
        rw [← hd_bound]
        exact mul_lt_mul_of_pos_right hr.2 hden
      nlinarith [min_le_left a b, mul_nonneg hr.1.le hn]
    have hnb : r * (n : ℝ) ≤ b := by
      have hprod : r * ((m : ℝ) + (n : ℝ) + 1) < min a b := by
        rw [← hd_bound]
        exact mul_lt_mul_of_pos_right hr.2 hden
      nlinarith [min_le_right a b, mul_nonneg hr.1.le hm]
    have h := hlap (r * m) ⟨mul_nonneg hr.1.le hm, hma⟩
      (r * n) ⟨mul_nonneg hr.1.le hn, hnb⟩
    simpa only [mgf, X, ← Real.exp_add, show ∀ x : ℝ × ℝ,
      -(r * ↑m) * x.1 + -(r * ↑n) * x.2 = r * -(↑m * x.1 + ↑n * x.2) by
        intro x; ring] using h
  have hloc : mgf X μ =ᶠ[𝓝 (d / 2)] mgf X ν := by
    filter_upwards [isOpen_Ioo.eventually_mem (show d / 2 ∈ Ioo (0 : ℝ) d by
      constructor <;> linarith)] with r hr
    exact heq r hr
  have hglobal := hμana.eqOn_of_preconnected_of_eventuallyEq hνana
    isPreconnected_Ioi (show d / 2 ∈ Ioi (0 : ℝ) by change 0 < d / 2; linarith) hloc
  have h := hglobal (show (1 : ℝ) ∈ Ioi 0 by norm_num)
  simpa only [mgf, X, one_mul, ← Real.exp_add,
    show ∀ x : ℝ × ℝ, -(↑m * x.1 + ↑n * x.2) = -↑m * x.1 + -↑n * x.2 by
      intro x; ring] using h

end Rhone.Statistics.Identifiability
