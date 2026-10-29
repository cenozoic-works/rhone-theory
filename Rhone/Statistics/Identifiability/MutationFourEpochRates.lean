/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationFourEpochConvergence

/-! # Piecewise rates of the four-epoch family and its matrix-exponential product form -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

noncomputable def fourEpochRate (ε δ M A τ t : ℝ) : ℝ :=
  if t < ε then δ + A / ε else if t < τ then δ
    else if t < τ + ε then δ + M / ε else δ

theorem fourEpochRate_lower {ε δ M A τ : ℝ} (hε : 0 < ε)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (t : ℝ) :
    δ ≤ fourEpochRate ε δ M A τ t := by
  unfold fourEpochRate
  split_ifs <;> linarith [div_nonneg hM hε.le, div_nonneg hA hε.le]

theorem fourEpochRate_pos {ε δ M A τ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hA : 0 ≤ A) (t : ℝ) :
    0 < fourEpochRate ε δ M A τ t :=
  hδ.trans_le (fourEpochRate_lower hε hM hA t)

theorem fourEpochRate_upper {ε δ M A τ : ℝ} (hε : 0 < ε)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (t : ℝ) :
    fourEpochRate ε δ M A τ t ≤ δ + (A + M) / ε := by
  have hMε := div_nonneg hM hε.le
  have hAε := div_nonneg hA hε.le
  unfold fourEpochRate
  rw [add_div]
  split_ifs <;> linarith

theorem fourEpochSize_bounds {ε δ M A τ c : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hc : 0 < c) (t : ℝ) :
    0 < c / (δ + (A + M) / ε) ∧
      c / (δ + (A + M) / ε) ≤ c / fourEpochRate ε δ M A τ t ∧
      c / fourEpochRate ε δ M A τ t ≤ c / δ := by
  have hp := fourEpochRate_pos (τ := τ) hε hδ hM hA t
  have hlo := fourEpochRate_lower (δ := δ) (τ := τ) hε hM hA t
  have hup := fourEpochRate_upper (δ := δ) (τ := τ) hε hM hA t
  exact ⟨div_pos hc (hp.trans_le hup), div_le_div_of_nonneg_left hc.le hp hup,
    div_le_div_of_nonneg_left hc.le hδ hlo⟩

theorem fourEpochVector_eq_exp_product {ε : ℝ} (hε : ε ≠ 0)
    (δ M r k : ℝ) (v : State → ℝ) (x : ℝ × ℝ) :
    fourEpochVector ε δ M r k v x =
      NormedSpace.exp (ε • B (δ + x.1 / ε) r k) *ᵥ
        (NormedSpace.exp ((x.2 - ε) • B δ r k) *ᵥ
          (NormedSpace.exp (ε • B (δ + M / ε) r k) *ᵥ v)) := by
  rw [add_comm δ (x.1 / ε), add_comm δ (M / ε),
    scaled_pulse_generator_eq hε, scaled_pulse_generator_eq hε]
  rfl

theorem pulseScale_pos {n : ℕ} (hn : 0 < n) : 0 < pulseScale n := by
  unfold pulseScale
  exact inv_pos.mpr (Nat.cast_pos.mpr hn)

theorem eventually_pulseScale_lt {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in Filter.atTop, 0 < pulseScale n ∧ pulseScale n < τ ∧ 0 < (n : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ),
    (tendsto_order.1 pulseScale_tendsto_zero).2 τ hτ] with n hn hsmall
  exact ⟨pulseScale_pos hn, hsmall, Nat.cast_pos.mpr hn⟩

end Rhone.Statistics.Identifiability.MutationPulseKernel
