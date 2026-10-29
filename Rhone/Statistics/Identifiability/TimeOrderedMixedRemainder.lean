/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeOrderedMixedIdentity
public import Rhone.Statistics.Identifiability.TimeOrderedRemainder

/-! # Mixed time-ordered remainder with an extra small-horizon factor -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def orderedTwoMarkIntegral (P R : ℝ → Matrix ι ι ℝ) (s t : ℝ) : Matrix ι ι ℝ :=
  (∫ u in s..t, ∫ v in u..t, P u * R v) +
    (∫ u in s..t, ∫ v in s..u, R v * P u)

set_option maxHeartbeats 800000 in
theorem inhomogeneousTransition_mixed_remainder_le
    (C P R : ℝ → Matrix ι ι ℝ)
    (hC : ∀ i j, Continuous (fun t => C t i j))
    (hP : ∀ i j, Continuous (fun t => P t i j))
    (hR : ∀ i j, Continuous (fun t => R t i j))
    {s t K : ℝ} (hst : s ≤ t) (hK : 0 ≤ K)
    (hbC : HasContractiveBoundOn C s t K)
    (hbCP : HasContractiveBoundOn (C + P) s t K)
    (hbCR : HasContractiveBoundOn (C + R) s t K)
    (hbD : HasContractiveBoundOn (C + P + R) s t K) :
    ‖inhomogeneousTransition (C + P + R) s t -
        inhomogeneousTransition (C + P) s t -
        inhomogeneousTransition (C + R) s t + inhomogeneousTransition C s t -
        orderedTwoMarkIntegral P R s t‖ ≤
      2 * K * (t-s) * (∫ u in s..t, ‖P u‖) * (∫ v in s..t, ‖R v‖) := by
  have hCP : ∀ i j, Continuous (fun u => (C + P) u i j) :=
    fun i j => (hC i j).add (hP i j)
  have hCR : ∀ i j, Continuous (fun u => (C + R) u i j) :=
    fun i j => (hC i j).add (hR i j)
  have hD : ∀ i j, Continuous (fun u => (C + P + R) u i j) :=
    fun i j => (hCP i j).add (hR i j)
  have hPc : Continuous P := continuous_pi fun i => continuous_pi (hP i)
  have hRc : Continuous R := continuous_pi fun i => continuous_pi (hR i)
  let F : ℝ → ℝ → Matrix ι ι ℝ := fun u v =>
    inhomogeneousTransition (C + P + R) s u * P u *
      inhomogeneousTransition (C + R) u v * R v * inhomogeneousTransition C v t
  let G : ℝ → ℝ → Matrix ι ι ℝ := fun u v =>
    inhomogeneousTransition (C + P + R) s v * R v *
      inhomogeneousTransition (C + P) v u * P u * inhomogeneousTransition C u t
  have hFc : Continuous (Function.uncurry F) := by
    exact (((((inhomogeneousTransition_continuous _ hD).comp
      (continuous_const.prodMk continuous_fst)).mul (hPc.comp continuous_fst)).mul
      (inhomogeneousTransition_continuous _ hCR)).mul (hRc.comp continuous_snd)).mul
      ((inhomogeneousTransition_continuous _ hC).comp (continuous_snd.prodMk continuous_const))
  have hGc : Continuous (Function.uncurry G) := by
    exact (((((inhomogeneousTransition_continuous _ hD).comp
      (continuous_const.prodMk continuous_snd)).mul (hRc.comp continuous_snd)).mul
      ((inhomogeneousTransition_continuous _ hCP).comp
        (continuous_snd.prodMk continuous_fst))).mul (hPc.comp continuous_fst)).mul
      ((inhomogeneousTransition_continuous _ hC).comp (continuous_fst.prodMk continuous_const))
  have hPR : Continuous (Function.uncurry (fun u v => P u * R v)) :=
    (hPc.comp continuous_fst).mul (hRc.comp continuous_snd)
  have hRP : Continuous (Function.uncurry (fun u v => R v * P u)) :=
    (hRc.comp continuous_snd).mul (hPc.comp continuous_fst)
  have hFbound : ‖∫ u in s..t, ∫ v in u..t, F u v - P u * R v‖ ≤
      K * (t-s) * (∫ u in s..t, ‖P u‖) * (∫ v in s..t, ‖R v‖) := by
    apply norm_integral_integral_upper_le_of_norm_le _ _ _ hPc.norm hRc.norm hst
      (mul_nonneg hK (sub_nonneg.mpr hst))
      (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    intro u v hsu huv hvt
    exact norm_transition_two_insertions_sub_le _ _ _ hD hCR hC hbD hbCR hbC
      hsu huv hvt (P u) (R v)
  have hGbound : ‖∫ u in s..t, ∫ v in s..u, G u v - R v * P u‖ ≤
      K * (t-s) * (∫ u in s..t, ‖P u‖) * (∫ v in s..t, ‖R v‖) := by
    apply norm_integral_integral_lower_le_of_norm_le _ _ _ hPc.norm hRc.norm hst
      (mul_nonneg hK (sub_nonneg.mpr hst))
      (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    intro u v hsv hvu hut
    have h := norm_transition_two_insertions_sub_le _ _ _ hD hCP hC hbD hbCP hbC
      hsv hvu hut (R v) (P u)
    exact h.trans_eq (by ring)
  rw [inhomogeneousTransition_mixed_sub_eq_integral C P R hC hP hR s t]
  change ‖((∫ u in s..t, ∫ v in u..t, F u v) + (∫ u in s..t, ∫ v in s..u, G u v)) -
    ((∫ u in s..t, ∫ v in u..t, P u * R v) + (∫ u in s..t, ∫ v in s..u, R v * P u))‖ ≤ _
  rw [show ∀ a b c d : Matrix ι ι ℝ, (a+b)-(c+d) = (a-c)+(b-d) by intros; abel]
  rw [integral_integral_upper_sub F _ hFc hPR, integral_integral_lower_sub G _ hGc hRP]
  exact (norm_add_le _ _).trans ((add_le_add hFbound hGbound).trans_eq (by ring))

omit [DecidableEq ι] in
theorem orderedTwoMarkIntegral_smul (P R : ℝ → Matrix ι ι ℝ) (a b s t : ℝ) :
    orderedTwoMarkIntegral (fun u => a • P u) (fun u => b • R u) s t =
      (a*b) • orderedTwoMarkIntegral P R s t := by
  simp only [orderedTwoMarkIntegral, smul_mul_assoc, mul_smul_comm, smul_smul,
    intervalIntegral.integral_smul, smul_add]
  rw [mul_comm b a]

theorem integral_norm_scalar_mark
    (q : ℝ → ℝ) (M : Matrix ι ι ℝ) {a s t : ℝ}
    (ha : 0 ≤ a) (hst : s ≤ t) (hq : ∀ u ∈ Icc s t, 0 ≤ q u) :
    (∫ u in s..t, ‖(a * q u) • M‖) = a * ‖M‖ * (∫ u in s..t, q u) := by
  calc
    _ = ∫ u in s..t, (a * ‖M‖) * q u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hst] at hu
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha (hq u hu))]
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

set_option maxHeartbeats 800000 in
theorem inhomogeneousTransition_scalar_mixed_remainder_le
    (C : ℝ → Matrix ι ι ℝ) (q r : ℝ → ℝ) (M R : Matrix ι ι ℝ)
    (hC : ∀ i j, Continuous (fun t => C t i j)) (hq : Continuous q) (hr : Continuous r)
    {a b s t K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hst : s ≤ t) (hK : 0 ≤ K)
    (hq0 : ∀ u ∈ Icc s t, 0 ≤ q u) (hr0 : ∀ u ∈ Icc s t, 0 ≤ r u)
    (hbC : HasContractiveBoundOn C s t K)
    (hbCM : HasContractiveBoundOn (C + fun u => (a * q u) • M) s t K)
    (hbCR : HasContractiveBoundOn (C + fun u => (b * r u) • R) s t K)
    (hbD : HasContractiveBoundOn
      (C + (fun u => (a * q u) • M) + fun u => (b * r u) • R) s t K) :
    ‖inhomogeneousTransition
        (C + (fun u => (a * q u) • M) + fun u => (b * r u) • R) s t -
      inhomogeneousTransition (C + fun u => (a * q u) • M) s t -
      inhomogeneousTransition (C + fun u => (b * r u) • R) s t +
      inhomogeneousTransition C s t -
      (a*b) • orderedTwoMarkIntegral (fun u => q u • M) (fun u => r u • R) s t‖ ≤
      (2 * K * ‖M‖ * ‖R‖) * a * b * (t-s) *
        (∫ u in s..t, q u) * (∫ u in s..t, r u) := by
  have hM : ∀ i j, Continuous (fun u => ((a * q u) • M) i j) :=
    fun i j => (continuous_const.mul hq).mul continuous_const
  have hR : ∀ i j, Continuous (fun u => ((b * r u) • R) i j) :=
    fun i j => (continuous_const.mul hr).mul continuous_const
  have h := inhomogeneousTransition_mixed_remainder_le C
    (fun u => (a * q u) • M) (fun u => (b * r u) • R) hC hM hR
    hst hK hbC hbCM hbCR hbD
  have hi := orderedTwoMarkIntegral_smul (fun u => q u • M) (fun u => r u • R) a b s t
  simp only [smul_smul] at hi
  rw [hi, integral_norm_scalar_mark q M ha hst hq0,
    integral_norm_scalar_mark r R hb hst hr0] at h
  exact h.trans_eq (by ring)

theorem norm_affine_marks_le
    (C M R : Matrix ι ι ℝ) {a b q r Cbar qbar rbar : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) qbar) (hr : r ∈ Icc (0 : ℝ) rbar)
    (hC : ‖C‖ ≤ Cbar) :
    ‖C + (a*q) • M + (b*r) • R‖ ≤ Cbar + qbar * ‖M‖ + rbar * ‖R‖ := by
  have haq : a*q ≤ qbar :=
    (mul_le_mul_of_nonneg_right ha.2 hq.1).trans (by simpa only [one_mul] using hq.2)
  have hbr : b*r ≤ rbar :=
    (mul_le_mul_of_nonneg_right hb.2 hr.1).trans (by simpa only [one_mul] using hr.2)
  calc
    _ ≤ ‖C‖ + ‖(a*q) • M‖ + ‖(b*r) • R‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖C‖ + (a*q) * ‖M‖ + (b*r) * ‖R‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ha.1 hq.1), abs_of_nonneg (mul_nonneg hb.1 hr.1)]
    _ ≤ _ := add_le_add (add_le_add hC (mul_le_mul_of_nonneg_right haq (norm_nonneg _)))
      (mul_le_mul_of_nonneg_right hbr (norm_nonneg _))

end Rhone.Statistics.Identifiability
