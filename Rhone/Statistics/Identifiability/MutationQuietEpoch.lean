/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulseDerivative

/-! # Uniform value and time derivative bounds for a quiet epoch -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

noncomputable def quietEpoch (τ ε δ r k : ℝ) : Matrix State State ℝ :=
  NormedSpace.exp ((τ - ε) • B δ r k)

noncomputable def quietLimitEpoch (τ r k : ℝ) : Matrix State State ℝ :=
  NormedSpace.exp (τ • B 0 r k)

theorem B_sub_zero (δ r k : ℝ) : B δ r k - B 0 r k = δ • C := by
  simp only [B, G, zero_smul, zero_add]
  abel

theorem B_zero_norm_le {r k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖B 0 r k‖ ≤ 4*r + 2*k := by
  simpa using B_norm_le (δ := 0) (by positivity) hr hk

theorem B_sub_zero_norm {δ : ℝ} (hδ : 0 ≤ δ) (r k : ℝ) :
    ‖B δ r k - B 0 r k‖ = 12*δ := by
  rw [B_sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ, C_norm]
  ring

theorem quietEpoch_norm_le_one {τ ε δ r k : ℝ}
    (hετ : ε ≤ τ) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖quietEpoch τ ε δ r k‖ ≤ 1 :=
  exp_B_norm_le_one hδ hr hk (sub_nonneg.mpr hετ)

theorem quietLimitEpoch_norm_le_one {τ r k : ℝ}
    (hτ : 0 ≤ τ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖quietLimitEpoch τ r k‖ ≤ 1 :=
  exp_B_norm_le_one (by positivity) hr hk hτ

theorem quietEpoch_hasDerivAt (τ ε δ r k : ℝ) :
    HasDerivAt (fun t : ℝ => quietEpoch t ε δ r k)
      (B δ r k * quietEpoch τ ε δ r k) τ := by
  simpa only [quietEpoch, Function.comp_def, one_smul, id_eq] using
    (hasDerivAt_exp_smul_const' (B δ r k) (τ - ε)).scomp τ
      ((hasDerivAt_id τ).sub_const ε)

theorem quietLimitEpoch_hasDerivAt (τ r k : ℝ) :
    HasDerivAt (fun t : ℝ => quietLimitEpoch t r k)
      (B 0 r k * quietLimitEpoch τ r k) τ :=
  hasDerivAt_exp_smul_const' (B 0 r k) τ

theorem quietEpoch_error {τ ε δ r k T : ℝ}
    (hε : 0 ≤ ε) (hετ : ε ≤ τ) (hτT : τ ≤ T)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖quietEpoch τ ε δ r k - quietLimitEpoch τ r k‖ ≤
      12*δ*T + ε*(4*r + 2*k) := by
  have hτ : 0 ≤ τ := hε.trans hετ
  have hτε : 0 ≤ τ - ε := sub_nonneg.mpr hετ
  have hsum : τ • B 0 r k + ((τ - ε) • B δ r k - τ • B 0 r k) =
      (τ - ε) • B δ r k := by abel
  have h := ContractiveDuhamel.norm_exp_add_sub_exp_le_one
    (τ • B 0 r k) ((τ - ε) • B δ r k - τ • B 0 r k)
    (fun s hs => by
      rw [smul_smul]
      exact exp_B_norm_le_one (by positivity) hr hk (mul_nonneg hs.1 hτ))
    (fun s hs => by
      rw [hsum, smul_smul]
      exact exp_B_norm_le_one hδ hr hk (mul_nonneg hs.1 hτε))
  rw [hsum] at h
  change ‖quietEpoch τ ε δ r k - quietLimitEpoch τ r k‖ ≤
    ‖(τ - ε) • B δ r k - τ • B 0 r k‖ at h
  refine h.trans ?_
  have hsplit : (τ - ε) • B δ r k - τ • B 0 r k =
      (τ - ε) • (B δ r k - B 0 r k) - ε • B 0 r k := by
    rw [smul_sub, sub_smul]
    module
  rw [hsplit]
  calc
    _ ≤ ‖(τ - ε) • (B δ r k - B 0 r k)‖ + ‖ε • B 0 r k‖ := norm_sub_le _ _
    _ = (τ - ε) * (12*δ) + ε * ‖B 0 r k‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hτε, abs_of_nonneg hε, B_sub_zero_norm hδ]
    _ ≤ T * (12*δ) + ε*(4*r + 2*k) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by linarith : τ - ε ≤ T) (by positivity))
        (mul_le_mul_of_nonneg_left (B_zero_norm_le hr hk) hε)
    _ = _ := by ring

theorem quietEpoch_derivative_error {τ ε δ r k T : ℝ}
    (hε : 0 ≤ ε) (hετ : ε ≤ τ) (hτT : τ ≤ T)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖B δ r k * quietEpoch τ ε δ r k - B 0 r k * quietLimitEpoch τ r k‖ ≤
      12*δ + (4*r + 2*k)*(12*δ*T + ε*(4*r + 2*k)) := by
  have hT : 0 ≤ T := hε.trans (hετ.trans hτT)
  have hsplit : B δ r k * quietEpoch τ ε δ r k - B 0 r k * quietLimitEpoch τ r k =
      (B δ r k - B 0 r k) * quietEpoch τ ε δ r k +
        B 0 r k * (quietEpoch τ ε δ r k - quietLimitEpoch τ r k) := by
    noncomm_ring
  rw [hsplit]
  calc
    _ ≤ ‖(B δ r k - B 0 r k) * quietEpoch τ ε δ r k‖ +
        ‖B 0 r k * (quietEpoch τ ε δ r k - quietLimitEpoch τ r k)‖ := norm_add_le _ _
    _ ≤ ‖B δ r k - B 0 r k‖ * ‖quietEpoch τ ε δ r k‖ +
        ‖B 0 r k‖ * ‖quietEpoch τ ε δ r k - quietLimitEpoch τ r k‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (12*δ) * 1 + (4*r + 2*k)*(12*δ*T + ε*(4*r + 2*k)) := by
      apply add_le_add
      · rw [B_sub_zero_norm hδ]
        exact mul_le_mul_of_nonneg_left (quietEpoch_norm_le_one hετ hδ hr hk) (by positivity)
      · exact mul_le_mul (B_zero_norm_le hr hk)
          (quietEpoch_error hε hετ hτT hδ hr hk) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem quietEpoch_deriv_error {τ ε δ r k T : ℝ}
    (hε : 0 ≤ ε) (hετ : ε ≤ τ) (hτT : τ ≤ T)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖deriv (fun t : ℝ => quietEpoch t ε δ r k) τ -
      deriv (fun t : ℝ => quietLimitEpoch t r k) τ‖ ≤
      12*δ + (4*r + 2*k)*(12*δ*T + ε*(4*r + 2*k)) := by
  rw [(quietEpoch_hasDerivAt τ ε δ r k).deriv,
    (quietLimitEpoch_hasDerivAt τ r k).deriv]
  exact quietEpoch_derivative_error hε hετ hτT hδ hr hk

end Rhone.Statistics.Identifiability.MutationPulseKernel
