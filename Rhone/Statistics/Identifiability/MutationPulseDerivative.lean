/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulsePerturbation
public import Rhone.Statistics.Identifiability.ContractiveInsertion

/-! # Uniform `C¹` control of the early pulse -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

open ContractiveDuhamel

theorem early_pulse_hasDerivAt (a ε δ r k : ℝ) :
    HasDerivAt (fun x : ℝ => NormedSpace.exp (x • C + ε • B δ r k))
      (expInsertion (a • C + ε • B δ r k) C) a :=
  hasDerivAt_exp_affine C (ε • B δ r k) a

theorem early_pulse_contDiff_one (ε δ r k : ℝ) :
    ContDiff ℝ 1 (fun a : ℝ => NormedSpace.exp (a • C + ε • B δ r k)) :=
  contDiff_one_exp_affine C (ε • B δ r k)

theorem early_pulse_derivative_error {a ε δ r k : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖expInsertion (a • C + ε • B δ r k) C - C * NormedSpace.exp (a • C)‖ ≤
      12 * ε * (12*δ + 4*r + 2*k) := by
  have h := norm_expInsertion_add_sub_le (a • C) (ε • B δ r k) C
    (fun s hs => exp_C_norm_le_one ha hs.1)
    (fun s hs => by
      rw [pulse_generator_eq]
      exact exp_B_norm_le_one (add_nonneg ha (mul_nonneg hε hδ))
        (mul_nonneg hε hr) (mul_nonneg hε hk) hs.1)
  rw [expInsertion_smul_self] at h
  refine h.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε, C_norm]
  calc
    ε * ‖B δ r k‖ * 12 ≤ (ε * (12*δ + 4*r + 2*k)) * 12 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (B_norm_le hδ hr hk) hε)
        (by positivity)
    _ = _ := by ring

theorem early_pulse_deriv_error {a ε δ r k : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖deriv (fun x : ℝ => NormedSpace.exp (x • C + ε • B δ r k)) a -
      C * NormedSpace.exp (a • C)‖ ≤ 12 * ε * (12*δ + 4*r + 2*k) := by
  rw [(early_pulse_hasDerivAt a ε δ r k).deriv]
  exact early_pulse_derivative_error ha hε hδ hr hk

end Rhone.Statistics.Identifiability.MutationPulseKernel
