/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulseDerivative
public import Rhone.Statistics.Identifiability.MutationQuietEpoch
public import Rhone.Statistics.Identifiability.MutationMomentSurjectivity

/-! # Calculus of the mutation four-epoch vector: derivative bounds and pulse-scale limits -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
open Rhone.Statistics.Identifiability.ContractiveDuhamel

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

abbrev Mat := Matrix State State ℝ
abbrev Vec := State → ℝ

noncomputable def applyVec (v : Vec) : Mat →L[ℝ] Vec :=
  ((Matrix.mulVecBilin ℝ ℝ).flip v).toContinuousLinearMap

@[simp] theorem applyVec_apply (v : Vec) (Q : Mat) : applyVec v Q = Q *ᵥ v := rfl

theorem separated_mulVec_hasFDerivAt
    (E Q : ℝ → Mat) (a t : ℝ) (Ea Qt : Mat) (v : Vec)
    (hE : HasDerivAt E Ea a) (hQ : HasDerivAt Q Qt t) :
    HasFDerivAt (fun x : ℝ × ℝ => E x.1 *ᵥ (Q x.2 *ᵥ v))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Ea *ᵥ (Q t *ᵥ v)) +
       (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (E a *ᵥ (Qt *ᵥ v))) (a,t) := by
  have he := hE.hasFDerivAt.comp (a,t) (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hq := hQ.hasFDerivAt.comp (a,t) (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hh := (applyVec v).hasFDerivAt.comp (a,t) (he.mul' hq)
  have hf : (fun x : ℝ × ℝ => E x.1 *ᵥ (Q x.2 *ᵥ v)) =
      (applyVec v) ∘ (E ∘ (ContinuousLinearMap.fst ℝ ℝ ℝ) *
        Q ∘ (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    funext x
    simp [Function.comp_def, Matrix.mulVec_mulVec]
  rw [hf]
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro x
  change x.1 • (Ea *ᵥ (Q t *ᵥ v)) + x.2 • (E a *ᵥ (Qt *ᵥ v)) =
    (E a * (x.2 • Qt) + (x.1 • Ea) * Q t) *ᵥ v
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
    add_comm]

theorem coordinate_derivative_norm_le (a t : Vec) :
    ‖(ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a +
       (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight t‖ ≤ ‖a‖ + ‖t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  calc
    _ = ‖x.1 • a + x.2 • t‖ := rfl
    _ ≤ ‖x.1 • a‖ + ‖x.2 • t‖ := norm_add_le _ _
    _ = ‖x.1‖ * ‖a‖ + ‖x.2‖ * ‖t‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖x‖ * ‖a‖ + ‖x‖ * ‖t‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_snd_le x) (norm_nonneg _))
    _ = (‖a‖ + ‖t‖) * ‖x‖ := by ring

theorem uniformlyOn_of_eventually_norm_sub_le
    {α F : Type*} [NormedAddCommGroup F] {S : Set α}
    {f : ℕ → α → F} {g : α → F} {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (hbound : ∀ᶠ n in Filter.atTop, ∀ x ∈ S, ‖f n x - g x‖ ≤ e n) :
    TendstoUniformlyOn f g Filter.atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hbound, (tendsto_order.1 he).2 ε hε] with n hn hen
  intro x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (hn x hx).trans_lt hen

noncomputable def pulseScale (n : ℕ) : ℝ := (n : ℝ)⁻¹

theorem pulseScale_nonneg (n : ℕ) : 0 ≤ pulseScale n := by
  unfold pulseScale
  positivity

theorem pulseScale_tendsto_zero :
    Filter.Tendsto pulseScale Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem exp_neg_nat_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) Filter.atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp
    (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

theorem pulseScale_eventually_le {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n in Filter.atTop, pulseScale n ≤ t :=
  ((tendsto_order.1 pulseScale_tendsto_zero).2 t ht).mono fun _ h => h.le

theorem compact_positive_time_bounds {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, 0 < x.2) :
    ∃ t > 0, ∃ T : ℝ, ∀ x ∈ K, t ≤ x.2 ∧ x.2 ≤ T := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    exact ⟨a.2, hpos a ha, b.2, fun x hx => ⟨hmin hx, hmax hx⟩⟩
  · refine ⟨1, zero_lt_one, 1, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

end Rhone.Statistics.Identifiability.MutationPulseKernel
