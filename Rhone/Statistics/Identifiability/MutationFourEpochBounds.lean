/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationQuietEpoch

/-! # Uniform value and parameter-derivative bounds for the four-epoch matrix family -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

open ContractiveDuhamel

noncomputable def fourEpochVector (ε δ M r k : ℝ) (v : State → ℝ)
    (x : ℝ × ℝ) : State → ℝ :=
  NormedSpace.exp (x.1 • C + ε • B δ r k) *ᵥ
    (quietEpoch x.2 ε δ r k *ᵥ
      (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v))

noncomputable def idealVector (r k : ℝ) (x : ℝ × ℝ) : State → ℝ :=
  NormedSpace.exp (x.1 • C) *ᵥ
    (quietLimitEpoch x.2 r k *ᵥ (fun _ => 1))

noncomputable def fourEpochPartialA (ε δ M r k : ℝ) (v : State → ℝ)
    (x : ℝ × ℝ) : State → ℝ :=
  expInsertion (x.1 • C + ε • B δ r k) C *ᵥ
    (quietEpoch x.2 ε δ r k *ᵥ
      (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v))

noncomputable def idealPartialA (r k : ℝ) (x : ℝ × ℝ) : State → ℝ :=
  (C * NormedSpace.exp (x.1 • C)) *ᵥ
    (quietLimitEpoch x.2 r k *ᵥ (fun _ => 1))

noncomputable def fourEpochPartialT (ε δ M r k : ℝ) (v : State → ℝ)
    (x : ℝ × ℝ) : State → ℝ :=
  NormedSpace.exp (x.1 • C + ε • B δ r k) *ᵥ
    ((B δ r k * quietEpoch x.2 ε δ r k) *ᵥ
      (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v))

noncomputable def idealPartialT (r k : ℝ) (x : ℝ × ℝ) : State → ℝ :=
  NormedSpace.exp (x.1 • C) *ᵥ
    ((B 0 r k * quietLimitEpoch x.2 r k) *ᵥ (fun _ => 1))

def earlyEpochError (ε δ r k : ℝ) : ℝ := ε*(12*δ + 4*r + 2*k)
def quietEpochError (ε δ r k T : ℝ) : ℝ := 12*δ*T + ε*(4*r + 2*k)
noncomputable def lateEpochError (ε δ M r k : ℝ) : ℝ :=
  2 * Real.exp (-M) + earlyEpochError ε δ r k
noncomputable def fourEpochError (ε δ M r k T : ℝ) : ℝ :=
  earlyEpochError ε δ r k + quietEpochError ε δ r k T + lateEpochError ε δ M r k

theorem mulVec_sub_norm_le (A A₀ : Matrix State State ℝ) (v v₀ : State → ℝ) :
    ‖A *ᵥ v - A₀ *ᵥ v₀‖ ≤ ‖A - A₀‖*‖v‖ + ‖A₀‖*‖v - v₀‖ := by
  have heq : A *ᵥ v - A₀ *ᵥ v₀ = (A-A₀) *ᵥ v + A₀ *ᵥ (v-v₀) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans
    (add_le_add (Matrix.linfty_opNorm_mulVec _ _) (Matrix.linfty_opNorm_mulVec _ _))

theorem mulVec_sub_norm_bound {A A₀ : Matrix State State ℝ} {v v₀ : State → ℝ}
    {a b c d : ℝ} (hA : ‖A - A₀‖ ≤ a) (hA₀ : ‖A₀‖ ≤ b)
    (hv : ‖v‖ ≤ c) (hd : ‖v - v₀‖ ≤ d) :
    ‖A *ᵥ v - A₀ *ᵥ v₀‖ ≤ a*c + b*d := by
  refine (mulVec_sub_norm_le A A₀ v v₀).trans ?_
  exact add_le_add
    (mul_le_mul hA hv (norm_nonneg _) ((norm_nonneg _).trans hA))
    (mul_le_mul hA₀ hd (norm_nonneg _) ((norm_nonneg _).trans hA₀))

theorem mulVec_norm_bound {A : Matrix State State ℝ} {v : State → ℝ}
    {a b : ℝ} (hA : ‖A‖ ≤ a) (hv : ‖v‖ ≤ b) : ‖A *ᵥ v‖ ≤ a*b :=
  (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul hA hv (norm_nonneg _) ((norm_nonneg _).trans hA))

theorem pulse_exp_norm_le_one {a ε δ r k : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖NormedSpace.exp (a • C + ε • B δ r k)‖ ≤ 1 := by
  rw [pulse_generator_eq]
  simpa only [one_smul] using exp_B_norm_le_one
    (add_nonneg ha (mul_nonneg hε hδ)) (mul_nonneg hε hr)
    (mul_nonneg hε hk) (t := 1) (by positivity)

theorem pure_exp_norm_le_one {a : ℝ} (ha : 0 ≤ a) :
    ‖NormedSpace.exp (a • C)‖ ≤ 1 := by
  simpa only [one_smul] using exp_C_norm_le_one ha (t := 1) (by positivity)

theorem late_pulse_vector_norm_le_one (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    {M ε δ r k : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v‖ ≤ 1 := by
  simpa using mulVec_norm_bound (pulse_exp_norm_le_one hM hε hδ hr hk)
    (payoff_norm_le_one v hv0 hv1)

theorem quiet_late_vector_norm_le_one (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    {τ ε δ M r k : ℝ} (hετ : ε ≤ τ) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖quietEpoch τ ε δ r k *ᵥ (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v)‖ ≤ 1 := by
  simpa using mulVec_norm_bound (quietEpoch_norm_le_one hετ hδ hr hk)
    (late_pulse_vector_norm_le_one v hv0 hv1 hM hε hδ hr hk)

theorem quiet_late_vector_error (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {τ ε δ M r k T : ℝ} (hε : 0 ≤ ε) (hετ : ε ≤ τ) (hτT : τ ≤ T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖quietEpoch τ ε δ r k *ᵥ (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v) -
      quietLimitEpoch τ r k *ᵥ (fun _ => 1)‖ ≤
      quietEpochError ε δ r k T + lateEpochError ε δ M r k := by
  simpa only [mul_one, one_mul, quietEpochError, lateEpochError, earlyEpochError] using
    mulVec_sub_norm_bound
      (quietEpoch_error hε hετ hτT hδ hr hk)
      (quietLimitEpoch_norm_le_one (hε.trans hετ) hr hk)
      (late_pulse_vector_norm_le_one v hv0 hv1 hM hε hδ hr hk)
      (late_pulse_norm_bound v hv0 hv1 hvabs hM hε hδ hr hk)

theorem fourEpochVector_error (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {x : ℝ × ℝ} {ε δ M r k T : ℝ}
    (hA : 0 ≤ x.1) (hε : 0 ≤ ε) (hετ : ε ≤ x.2) (hτT : x.2 ≤ T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖fourEpochVector ε δ M r k v x - idealVector r k x‖ ≤
      fourEpochError ε δ M r k T := by
  have h := mulVec_sub_norm_bound
    (late_pulse_operator_error hA hε hδ hr hk)
    (pure_exp_norm_le_one hA)
    (quiet_late_vector_norm_le_one v hv0 hv1 hετ hM hε hδ hr hk)
    (quiet_late_vector_error v hv0 hv1 hvabs hε hετ hτT hM hδ hr hk)
  simpa only [fourEpochVector, idealVector, fourEpochError, earlyEpochError,
    mul_one, one_mul, add_assoc] using h

theorem fourEpochPartialA_error (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {x : ℝ × ℝ} {ε δ M r k T : ℝ}
    (hA : 0 ≤ x.1) (hε : 0 ≤ ε) (hετ : ε ≤ x.2) (hτT : x.2 ≤ T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖fourEpochPartialA ε δ M r k v x - idealPartialA r k x‖ ≤
      12 * fourEpochError ε δ M r k T := by
  have hideal : ‖C * NormedSpace.exp (x.1 • C)‖ ≤ 12 := by
    calc
      _ ≤ ‖C‖ * ‖NormedSpace.exp (x.1 • C)‖ := norm_mul_le _ _
      _ ≤ 12 * 1 := by rw [C_norm]; exact mul_le_mul_of_nonneg_left (pure_exp_norm_le_one hA) (by
        positivity)
      _ = 12 := by ring
  have h := mulVec_sub_norm_bound
    (early_pulse_derivative_error hA hε hδ hr hk) hideal
    (quiet_late_vector_norm_le_one v hv0 hv1 hετ hM hε hδ hr hk)
    (quiet_late_vector_error v hv0 hv1 hvabs hε hετ hτT hM hδ hr hk)
  change ‖fourEpochPartialA ε δ M r k v x - idealPartialA r k x‖ ≤ _ at h
  refine h.trans_eq ?_
  unfold fourEpochError earlyEpochError
  ring

theorem fourEpochPartialT_error (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {x : ℝ × ℝ} {ε δ M r k T : ℝ}
    (hA : 0 ≤ x.1) (hε : 0 ≤ ε) (hετ : ε ≤ x.2) (hτT : x.2 ≤ T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖fourEpochPartialT ε δ M r k v x - idealPartialT r k x‖ ≤
      (12*δ + 4*r + 2*k)*earlyEpochError ε δ r k + 12*δ +
        (4*r + 2*k)*(quietEpochError ε δ r k T + lateEpochError ε δ M r k) := by
  have hτ : 0 ≤ x.2 := hε.trans hετ
  have hBQ : ‖B δ r k * quietEpoch x.2 ε δ r k‖ ≤ 12*δ + 4*r + 2*k := by
    calc
      _ ≤ ‖B δ r k‖ * ‖quietEpoch x.2 ε δ r k‖ := norm_mul_le _ _
      _ ≤ (12*δ + 4*r + 2*k) * 1 :=
        mul_le_mul (B_norm_le hδ hr hk) (quietEpoch_norm_le_one hετ hδ hr hk)
          (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hB₀Q₀ : ‖B 0 r k * quietLimitEpoch x.2 r k‖ ≤ 4*r + 2*k := by
    calc
      _ ≤ ‖B 0 r k‖ * ‖quietLimitEpoch x.2 r k‖ := norm_mul_le _ _
      _ ≤ (4*r + 2*k) * 1 :=
        mul_le_mul (B_zero_norm_le hr hk) (quietLimitEpoch_norm_le_one hτ hr hk)
          (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hinnernorm : ‖(B δ r k * quietEpoch x.2 ε δ r k) *ᵥ
      (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v)‖ ≤ 12*δ + 4*r + 2*k := by
    simpa only [mul_one] using mulVec_norm_bound hBQ
      (late_pulse_vector_norm_le_one v hv0 hv1 hM hε hδ hr hk)
  have hinner := mulVec_sub_norm_bound
    (quietEpoch_derivative_error hε hετ hτT hδ hr hk) hB₀Q₀
    (late_pulse_vector_norm_le_one v hv0 hv1 hM hε hδ hr hk)
    (late_pulse_norm_bound v hv0 hv1 hvabs hM hε hδ hr hk)
  have h := mulVec_sub_norm_bound
    (late_pulse_operator_error hA hε hδ hr hk)
    (pure_exp_norm_le_one hA) hinnernorm hinner
  change ‖fourEpochPartialT ε δ M r k v x - idealPartialT r k x‖ ≤ _ at h
  refine h.trans_eq ?_
  unfold quietEpochError lateEpochError earlyEpochError
  ring

end Rhone.Statistics.Identifiability.MutationPulseKernel
