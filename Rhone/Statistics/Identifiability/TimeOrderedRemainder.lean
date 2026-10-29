/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeOrderedDuhamel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Quantitative local remainder estimates for ordered matrix insertions -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inhomogeneousTransition_sub_one_eq_integral
    (Q : ℝ → Matrix ι ι ℝ) (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s t : ℝ) :
    inhomogeneousTransition Q s t - 1 =
      ∫ u in s..t, inhomogeneousTransition Q s u * Q u := by
  have hQc : Continuous Q := continuous_pi fun i => continuous_pi (hQ i)
  have hc : Continuous (fun u => inhomogeneousTransition Q s u * Q u) :=
    ((inhomogeneousTransition_continuous Q hQ).comp
      (continuous_const.prodMk continuous_id)).mul hQc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => inhomogeneousTransition_matrix_hasDerivAt_right Q hQ s u)
    (hc.intervalIntegrable s t)
  simpa only [inhomogeneousTransition_self Q hQ] using h.symm

theorem inhomogeneousTransition_norm_sub_one_le
    (Q : ℝ → Matrix ι ι ℝ) (hQ : ∀ i j, Continuous (fun t => Q t i j))
    {s t K : ℝ} (hst : s ≤ t)
    (hU : ∀ u ∈ Icc s t, ‖inhomogeneousTransition Q s u‖ ≤ 1)
    (hK : ∀ u ∈ Icc s t, ‖Q u‖ ≤ K) :
    ‖inhomogeneousTransition Q s t - 1‖ ≤ K * (t-s) := by
  rw [inhomogeneousTransition_sub_one_eq_integral Q hQ]
  have hb : ∀ u ∈ Set.uIoc s t, ‖inhomogeneousTransition Q s u * Q u‖ ≤ K := by
    intro u hu
    rw [uIoc_of_le hst] at hu
    have hu' : u ∈ Icc s t := ⟨hu.1.le, hu.2⟩
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right (hU u hu') (norm_nonneg _)).trans
        (by simpa only [one_mul] using hK u hu'))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem norm_ordered_two_insertions_sub_le
    {𝔄 : Type*} [NormedRing 𝔄] (X Y Z P R : 𝔄)
    (hY : ‖Y‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) :
    ‖X * P * Y * R * Z - P * R‖ ≤
      (‖X-1‖ + ‖Y-1‖ + ‖Z-1‖) * ‖P‖ * ‖R‖ := by
  have heq : X * P * Y * R * Z - P * R =
      (X-1) * P * Y * R * Z + P * (Y-1) * R * Z + P * R * (Z-1) := by
    noncomm_ring
  rw [heq]
  have h₁ : ‖(X-1) * P * Y * R * Z‖ ≤ ‖X-1‖ * ‖P‖ * ‖R‖ := by
    calc
      _ ≤ ‖X-1‖ * ‖P‖ * ‖Y‖ * ‖R‖ * ‖Z‖ := by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ ‖X-1‖ * ‖P‖ * 1 * ‖R‖ * 1 := by gcongr
      _ = _ := by ring
  have h₂ : ‖P * (Y-1) * R * Z‖ ≤ ‖P‖ * ‖Y-1‖ * ‖R‖ := by
    calc
      _ ≤ ‖P‖ * ‖Y-1‖ * ‖R‖ * ‖Z‖ := by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ ‖P‖ * ‖Y-1‖ * ‖R‖ * 1 := by gcongr
      _ = _ := by ring
  have h₃ : ‖P * R * (Z-1)‖ ≤ ‖P‖ * ‖R‖ * ‖Z-1‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  calc
    _ ≤ (‖(X-1) * P * Y * R * Z‖ + ‖P * (Y-1) * R * Z‖) + ‖P * R * (Z-1)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖X-1‖ * ‖P‖ * ‖R‖ + ‖P‖ * ‖Y-1‖ * ‖R‖) + ‖P‖ * ‖R‖ * ‖Z-1‖ :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

def HasContractiveBoundOn (Q : ℝ → Matrix ι ι ℝ) (s t K : ℝ) : Prop :=
  (∀ u ∈ Icc s t, ‖Q u‖ ≤ K) ∧
    ∀ a b, s ≤ a → a ≤ b → b ≤ t → ‖inhomogeneousTransition Q a b‖ ≤ 1

theorem HasContractiveBoundOn.norm_sub_one_le
    {Q : ℝ → Matrix ι ι ℝ} (hQ : ∀ i j, Continuous (fun t => Q t i j))
    {s t K a b : ℝ} (h : HasContractiveBoundOn Q s t K)
    (hsa : s ≤ a) (hab : a ≤ b) (hbt : b ≤ t) :
    ‖inhomogeneousTransition Q a b - 1‖ ≤ K * (b-a) := by
  apply inhomogeneousTransition_norm_sub_one_le Q hQ hab
  · exact fun u hu => h.2 a u hsa hu.1 (hu.2.trans hbt)
  · exact fun u hu => h.1 u ⟨hsa.trans hu.1, hu.2.trans hbt⟩

theorem norm_transition_two_insertions_sub_le
    (A B C : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j))
    (hC : ∀ i j, Continuous (fun t => C t i j))
    {s u v t K : ℝ}
    (hAb : HasContractiveBoundOn A s t K)
    (hBb : HasContractiveBoundOn B s t K)
    (hCb : HasContractiveBoundOn C s t K)
    (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) (P R : Matrix ι ι ℝ) :
    ‖inhomogeneousTransition A s u * P * inhomogeneousTransition B u v * R *
        inhomogeneousTransition C v t - P * R‖ ≤ K * (t-s) * ‖P‖ * ‖R‖ := by
  calc
    _ ≤ (‖inhomogeneousTransition A s u - 1‖ +
        ‖inhomogeneousTransition B u v - 1‖ +
        ‖inhomogeneousTransition C v t - 1‖) * ‖P‖ * ‖R‖ :=
      norm_ordered_two_insertions_sub_le _ _ _ _ _
        (hBb.2 u v hsu huv hvt) (hCb.2 v t (hsu.trans huv) hvt le_rfl)
    _ ≤ (K*(u-s) + K*(v-u) + K*(t-v)) * ‖P‖ * ‖R‖ := by
      gcongr
      · exact hAb.norm_sub_one_le hA le_rfl hsu (huv.trans hvt)
      · exact hBb.norm_sub_one_le hB hsu huv hvt
      · exact hCb.norm_sub_one_le hC (hsu.trans huv) hvt le_rfl
    _ = _ := by ring

theorem norm_integral_integral_upper_le_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ℝ → E) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r)
    {s t L : ℝ} (hst : s ≤ t) (hL : 0 ≤ L)
    (hp0 : ∀ u ∈ Icc s t, 0 ≤ p u) (hr0 : ∀ u ∈ Icc s t, 0 ≤ r u)
    (hF : ∀ u v, s ≤ u → u ≤ v → v ≤ t → ‖F u v‖ ≤ L * p u * r v) :
    ‖∫ u in s..t, ∫ v in u..t, F u v‖ ≤
      L * (∫ u in s..t, p u) * (∫ v in s..t, r v) := by
  have hbound : ∀ u ∈ Icc s t,
      ‖∫ v in u..t, F u v‖ ≤ L * p u * (∫ v in s..t, r v) := by
    intro u hu
    calc
      _ ≤ ∫ v in u..t, L * p u * r v := by
        apply intervalIntegral.norm_integral_le_of_norm_le hu.2
        · exact Filter.Eventually.of_forall fun v hv => hF u v hu.1 hv.1.le hv.2
        · exact (continuous_const.mul hr).intervalIntegrable u t
      _ = L * p u * (∫ v in u..t, r v) := intervalIntegral.integral_const_mul _ _
      _ ≤ L * p u * (∫ v in s..t, r v) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL (hp0 u hu))
        apply intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
          exact hr0 v ⟨hv.1.le, hv.2⟩
        · exact hr.intervalIntegrable s t
  calc
    _ ≤ ∫ u in s..t, L * p u * (∫ v in s..t, r v) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hst
      · exact Filter.Eventually.of_forall fun u hu => hbound u ⟨hu.1.le, hu.2⟩
      · exact ((continuous_const.mul hp).mul continuous_const).intervalIntegrable s t
    _ = _ := by rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

theorem norm_integral_integral_lower_le_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ℝ → E) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r)
    {s t L : ℝ} (hst : s ≤ t) (hL : 0 ≤ L)
    (hp0 : ∀ u ∈ Icc s t, 0 ≤ p u) (hr0 : ∀ u ∈ Icc s t, 0 ≤ r u)
    (hF : ∀ u v, s ≤ v → v ≤ u → u ≤ t → ‖F u v‖ ≤ L * p u * r v) :
    ‖∫ u in s..t, ∫ v in s..u, F u v‖ ≤
      L * (∫ u in s..t, p u) * (∫ v in s..t, r v) := by
  have hbound : ∀ u ∈ Icc s t,
      ‖∫ v in s..u, F u v‖ ≤ L * p u * (∫ v in s..t, r v) := by
    intro u hu
    calc
      _ ≤ ∫ v in s..u, L * p u * r v := by
        apply intervalIntegral.norm_integral_le_of_norm_le hu.1
        · exact Filter.Eventually.of_forall fun v hv => hF u v hv.1.le hv.2 hu.2
        · exact (continuous_const.mul hr).intervalIntegrable s u
      _ = L * p u * (∫ v in s..u, r v) := intervalIntegral.integral_const_mul _ _
      _ ≤ L * p u * (∫ v in s..t, r v) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL (hp0 u hu))
        apply intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
          exact hr0 v ⟨hv.1.le, hv.2⟩
        · exact hr.intervalIntegrable s t
  calc
    _ ≤ ∫ u in s..t, L * p u * (∫ v in s..t, r v) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hst
      · exact Filter.Eventually.of_forall fun u hu => hbound u ⟨hu.1.le, hu.2⟩
      · exact ((continuous_const.mul hp).mul continuous_const).intervalIntegrable s t
    _ = _ := by rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

theorem continuous_integral_upper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → ℝ → E) (hF : Continuous (Function.uncurry F)) (t : ℝ) :
    Continuous (fun u => ∫ v in u..t, F u v) := by
  have h := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := t) hF continuous_id).neg
  have he : (fun u => ∫ v in u..t, F u v) = (fun u => -(∫ v in t..u, F u v)) := by
    funext u
    exact intervalIntegral.integral_symm t u (f := F u)
  rw [he]
  exact h

theorem integral_integral_upper_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F G : ℝ → ℝ → E)
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (s t : ℝ) :
    (∫ u in s..t, ∫ v in u..t, F u v) - (∫ u in s..t, ∫ v in u..t, G u v) =
      ∫ u in s..t, ∫ v in u..t, F u v - G u v := by
  rw [← intervalIntegral.integral_sub
    ((continuous_integral_upper F hF t).intervalIntegrable s t)
    ((continuous_integral_upper G hG t).intervalIntegrable s t)]
  apply intervalIntegral.integral_congr
  intro u _
  exact (intervalIntegral.integral_sub
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable u t)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable u t)).symm

theorem integral_integral_lower_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F G : ℝ → ℝ → E)
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (s t : ℝ) :
    (∫ u in s..t, ∫ v in s..u, F u v) - (∫ u in s..t, ∫ v in s..u, G u v) =
      ∫ u in s..t, ∫ v in s..u, F u v - G u v := by
  have hFi : Continuous (fun u => ∫ v in s..u, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := s) hF continuous_id
  have hGi : Continuous (fun u => ∫ v in s..u, G u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := s) hG continuous_id
  rw [← intervalIntegral.integral_sub (hFi.intervalIntegrable s t) (hGi.intervalIntegrable s t)]
  apply intervalIntegral.integral_congr
  intro u _
  exact (intervalIntegral.integral_sub
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable s u)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable s u)).symm

theorem hasContractiveBoundOn_of_subgenerator
    (Q : ℝ → Matrix ι ι ℝ) (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    (hr : ∀ u, 0 ≤ u → ∀ i, ∑ j, Q u i j ≤ 0)
    {s t K : ℝ} (hs : 0 ≤ s) (hK : ∀ u ∈ Icc s t, ‖Q u‖ ≤ K) :
    HasContractiveBoundOn Q s t K := by
  refine ⟨hK, fun a b hsa hab _ => ?_⟩
  exact finiteMatrix_norm_le_one_of_substochastic _
    (inhomogeneousTransition_nonneg Q hQ hn (hs.trans hsa) hab)
    (inhomogeneousTransition_row_sum_le_one Q hQ hn hr (hs.trans hsa) hab)

end Rhone.Statistics.Identifiability
