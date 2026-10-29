/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulseKernel
public import Rhone.Statistics.Identifiability.ContractiveDuhamel

/-! # Uniform late-pulse perturbation -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

theorem B_norm_le {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖B δ r k‖ ≤ 12*δ + 4*r + 2*k := by
  calc
    ‖B δ r k‖ ≤ ‖δ • C + r • R‖ + ‖k • D‖ := norm_sub_le _ _
    _ ≤ (‖δ • C‖ + ‖r • R‖) + ‖k • D‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = 12*δ + 4*r + 2*k := by
      rw [norm_smul, norm_smul, norm_smul, C_norm, R_norm, D_norm,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hδ, abs_of_nonneg hr, abs_of_nonneg hk]
      ring

theorem pulse_generator_eq (M ε δ r k : ℝ) :
    M • C + ε • B δ r k = B (M+ε*δ) (ε*r) (ε*k) := by
  simp only [B, G, smul_sub, smul_add, smul_smul, add_smul]
  abel

theorem exp_C_norm_le_one {M t : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • (M • C))‖ ≤ 1 := by
  simpa [B, G] using exp_B_norm_le_one (lam := M) (r := 0) (k := 0) hM
    (by positivity) (by positivity) ht

theorem late_pulse_operator_error {M ε δ r k : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖NormedSpace.exp (M • C + ε • B δ r k) - NormedSpace.exp (M • C)‖ ≤
      ε * (12*δ + 4*r + 2*k) := by
  have h := ContractiveDuhamel.norm_exp_add_sub_exp_le_one (M • C) (ε • B δ r k)
    (fun s hs => exp_C_norm_le_one hM hs.1)
    (fun s hs => by
      rw [pulse_generator_eq]
      exact exp_B_norm_le_one (add_nonneg hM (mul_nonneg hε hδ))
        (mul_nonneg hε hr) (mul_nonneg hε hk) hs.1)
  refine h.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (B_norm_le hδ hr hk) hε

theorem payoff_norm_le_one (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) : ‖v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  simpa [Real.norm_eq_abs, abs_of_nonneg (hv0 i)] using hv1 i

theorem late_pulse_norm_bound (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {M ε δ r k : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v - (fun _ => 1)‖ ≤
      2 * Real.exp (-M) + ε * (12*δ + 4*r + 2*k) := by
  have hvec : ‖(NormedSpace.exp (M • C + ε • B δ r k) -
      NormedSpace.exp (M • C)) *ᵥ v‖ ≤ ε * (12*δ + 4*r + 2*k) := by
    calc
      _ ≤ ‖NormedSpace.exp (M • C + ε • B δ r k) - NormedSpace.exp (M • C)‖ * ‖v‖ :=
        Matrix.linfty_opNorm_mulVec _ _
      _ ≤ (ε * (12*δ + 4*r + 2*k)) * 1 :=
        mul_le_mul (late_pulse_operator_error hM hε hδ hr hk)
          (payoff_norm_le_one v hv0 hv1) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hpure := pure_pulse_norm_bound v hv0 hv1 hvabs hM
  calc
    _ ≤ ‖NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v -
          NormedSpace.exp (M • C) *ᵥ v‖ +
        ‖NormedSpace.exp (M • C) *ᵥ v - (fun _ => 1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε * (12*δ + 4*r + 2*k) + 2 * Real.exp (-M) := by
      rw [← Matrix.sub_mulVec]
      exact add_le_add hvec hpure
    _ = _ := add_comm _ _

theorem scaled_pulse_generator_eq {ε : ℝ} (hε : ε ≠ 0) (M δ r k : ℝ) :
    ε • B (M/ε+δ) r k = M • C + ε • B δ r k := by
  have hm : ε * (M/ε+δ) = M+ε*δ := by field_simp
  rw [pulse_generator_eq]
  simp only [B, G, smul_sub, smul_add, smul_smul, hm]

theorem short_pulse_norm_bound (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {M ε δ r k : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖NormedSpace.exp (ε • B (M/ε+δ) r k) *ᵥ v - (fun _ => 1)‖ ≤
      2 * Real.exp (-M) + ε * (12*δ + 4*r + 2*k) := by
  rw [scaled_pulse_generator_eq hε.ne']
  exact late_pulse_norm_bound v hv0 hv1 hvabs hM hε.le hδ hr hk

end Rhone.Statistics.Identifiability.MutationPulseKernel
