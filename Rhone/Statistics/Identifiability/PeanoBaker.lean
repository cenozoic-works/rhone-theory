/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Peano–Baker series solution of linear ODEs: existence and regularity -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Nat

namespace Rhone.Statistics.Identifiability.PeanoBaker
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def term (A : ℝ → E →L[ℝ] E) (x : E) : ℕ → ℝ → E
  | 0, _ => x
  | n + 1, t => ∫ s in (0 : ℝ)..t, A s (term A x n s)

@[simp] theorem term_zero (A : ℝ → E →L[ℝ] E) (x : E) (t : ℝ) : term A x 0 t = x := rfl
@[simp] theorem term_succ (A : ℝ → E →L[ℝ] E) (x : E) (n : ℕ) (t : ℝ) :
    term A x (n+1) t = ∫ s in (0 : ℝ)..t, A s (term A x n s) := rfl
@[simp] theorem term_succ_at_zero (A : ℝ → E →L[ℝ] E) (x : E) (n : ℕ) :
    term A x (n+1) 0 = 0 := by simp

variable [CompleteSpace E]

theorem term_continuous (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) (n : ℕ) :
    Continuous (term A x n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc := hA.clm_apply ih
    exact continuous_iff_continuousAt.mpr fun t =>
      (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt

theorem term_succ_hasDerivAt (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E)
    (n : ℕ) (t : ℝ) : HasDerivAt (term A x (n+1)) (A t (term A x n t)) t := by
  have hc := hA.clm_apply (term_continuous A hA x n)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

omit [CompleteSpace E] in
theorem norm_term_le (A : ℝ → E →L[ℝ] E) (x : E) {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hA : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖term A x n t‖ ≤ (K * |t|)^n / (n.factorial : ℝ) * ‖x‖ := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [term_succ]
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t, (K^(n+1) / (n.factorial : ℝ) * ‖x‖) * |s|^n := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hs' : s ∈ Icc (-T) T :=
          (uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-T) T by constructor <;> linarith) ht)
            (uIoc_subset_uIcc hs)
        calc
          ‖A s (term A x n s)‖ ≤ ‖A s‖ * ‖term A x n s‖ := (A s).le_opNorm _
          _ ≤ K * ((K * |s|)^n / (n.factorial : ℝ) * ‖x‖) := mul_le_mul (hA s hs') (ih hs')
            (norm_nonneg _) hK
          _ = (K^(n+1) / (n.factorial : ℝ) * ‖x‖) * |s|^n := by rw [mul_pow, pow_succ]; ring
      _ = (K * |t|)^(n+1) / ((n+1).factorial : ℝ) * ‖x‖ := by
        rw [MeasureTheory.integral_const_mul]
        have hi : (∫ s in uIoc (0 : ℝ) t, |s|^n) = |t|^(n+1)/(n+1) := by
          simpa using (integral_pow_abs_sub_uIoc (a := 0) (b := t) (n := n))
        rw [hi, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

theorem term_summable (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) (t : ℝ) :
    Summable (fun n => term A x n t) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hA.continuousOn : ContinuousOn A (Icc (-|t|) |t|))
  have hzero : (0 : ℝ) ∈ Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have hK₀ : 0 ≤ K := (norm_nonneg (A 0)).trans (hK 0 hzero)
  apply ((Real.summable_pow_div_factorial (K * |t|)).mul_right ‖x‖).of_norm_bounded
  intro n
  exact norm_term_le A x hK₀ (abs_nonneg t) hK n ⟨neg_abs_le t, le_abs_self t⟩

noncomputable def solution (A : ℝ → E →L[ℝ] E) (x : E) (t : ℝ) : E :=
  ∑' n, term A x n t

theorem solution_zero (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) :
    solution A x 0 = x := by
  rw [solution, (term_summable A hA x 0).tsum_eq_zero_add]
  simp

theorem solution_hasDerivAt (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) (t : ℝ) :
    HasDerivAt (solution A x) (A t (solution A x t)) t := by
  let T : ℝ := |t| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hA.continuousOn : ContinuousOn A (Icc (-T) T))
  have hzero : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hK₀ : 0 ≤ K := (norm_nonneg (A 0)).trans (hK 0 hzero)
  let u : ℕ → ℝ := fun n => K * ((K * T)^n / (n.factorial : ℝ) * ‖x‖)
  have hu : Summable u :=
    ((Real.summable_pow_div_factorial (K * T)).mul_right ‖x‖).mul_left K
  have hbound : ∀ n y, y ∈ Ioo (-T) T → ‖A y (term A x n y)‖ ≤ u n := by
    intro n y hy
    have hy' : y ∈ Icc (-T) T := Ioo_subset_Icc_self hy
    calc
      ‖A y (term A x n y)‖ ≤ ‖A y‖ * ‖term A x n y‖ := (A y).le_opNorm _
      _ ≤ K * ((K * |y|)^n / (n.factorial : ℝ) * ‖x‖) :=
        mul_le_mul (hK y hy') (norm_term_le A x hK₀ hT.le hK n hy') (norm_nonneg _) hK₀
      _ ≤ u n := by
        dsimp [u]
        gcongr
        exact abs_le.mpr hy'
  have ht : t ∈ Ioo (-T) T := abs_lt.mp (by dsimp [T]; linarith)
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-T) T).isPreconnected
    (fun n y _ => term_succ_hasDerivAt A hA x n y) hbound
    (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT⟩)
    (show Summable (fun n => term A x (n+1) 0) by simp) ht
  have heq : solution A x = fun z => x + ∑' n, term A x (n+1) z := by
    funext z
    exact (term_summable A hA x z).tsum_eq_zero_add
  rw [← (A t).map_tsum (term_summable A hA x t)] at hd
  have hd' : HasDerivAt (fun z => x + ∑' n, term A x (n+1) z)
      (A t (solution A x t)) t := HasDerivAt.const_add x hd
  rw [← heq] at hd'
  exact hd'

theorem solution_continuous (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) :
    Continuous (solution A x) :=
  continuous_iff_continuousAt.mpr fun t => (solution_hasDerivAt A hA x t).continuousAt

theorem solution_contDiff (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) :
    ContDiff ℝ 1 (solution A x) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (solution_hasDerivAt A hA x t).differentiableAt, ?_⟩
  have heq : deriv (solution A x) = fun t => A t (solution A x t) := by
    funext t
    exact (solution_hasDerivAt A hA x t).deriv
  rw [heq]
  exact hA.clm_apply (solution_continuous A hA x)

theorem exists_global_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) :
    ∃ X : ℝ → E, X 0 = x ∧ Continuous X ∧
      ∀ t, HasDerivAt X (A t (X t)) t :=
  ⟨solution A x, solution_zero A hA x, solution_continuous A hA x,
    solution_hasDerivAt A hA x⟩

end Rhone.Statistics.Identifiability.PeanoBaker
