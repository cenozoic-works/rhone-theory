/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanMutationMoments

/-! # Endpoint bounds for mutation moments of integrable pan models -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Rhone.Statistics.Identifiability
namespace ProperIntegrablePanModel

variable (P : ProperIntegrablePanModel)

theorem jointLaw_ae_coordinates_pos :
    ∀ᵐ p ∂P.pre.jointLaw, 0 < p.1 ∧ 0 < p.2 := by
  have h : ∀ᵐ t ∂conditionalPairLaw P.rate (integrablePanClock P.rate) 0, 0 < t := by
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioi)
  have hf := h
  rw [← P.jointLaw_map_fst] at hf
  have hs := h
  rw [← P.jointLaw_map_snd] at hs
  exact (ae_of_ae_map measurable_fst.aemeasurable hf).and
    (ae_of_ae_map measurable_snd.aemeasurable hs)

theorem jointLaw_ae_laplace_bounds {k : ℝ} (hk : 0 < k) :
    ∀ᵐ p ∂P.pre.jointLaw,
      (0 < Real.exp (-k*p.1) ∧ Real.exp (-k*p.1) < 1) ∧
      (0 < Real.exp (-k*p.2) ∧ Real.exp (-k*p.2) < 1) := by
  filter_upwards [P.jointLaw_ae_coordinates_pos] with p hp
  exact ⟨⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hp.1)⟩,
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hp.2)⟩⟩

theorem fstLaplace_integrable {k : ℝ} (hk : 0 < k) :
    Integrable (fun p => Real.exp (-k*p.1)) P.pre.jointLaw := by
  let := P.jointLaw_probability
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
  simpa only [Real.norm_eq_abs, abs_of_pos hp.1.1] using hp.1.2.le

theorem sndLaplace_integrable {k : ℝ} (hk : 0 < k) :
    Integrable (fun p => Real.exp (-k*p.2)) P.pre.jointLaw := by
  let := P.jointLaw_probability
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
  simpa only [Real.norm_eq_abs, abs_of_pos hp.2.1] using hp.2.2.le

theorem firstMutationObservable_integrable_of_proper {k : ℝ} (hk : 0 < k) (L : ℝ) :
    Integrable (firstMutationObservable L k) P.pre.jointLaw := by
  let := P.jointLaw_probability
  exact ((integrable_const (1 : ℝ)).sub (P.fstLaplace_integrable hk)).const_mul L

theorem productMutationObservable_integrable_of_proper {k : ℝ} (hk : 0 < k) (L : ℝ) :
    Integrable (productMutationObservable L k) P.pre.jointLaw := by
  let := P.jointLaw_probability
  refine (integrable_const (L^2)).mono' (by unfold productMutationObservable; fun_prop) ?_
  filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
  have h1 : 0 ≤ 1 - Real.exp (-k*p.1) := sub_nonneg.mpr hp.1.2.le
  have h2 : 0 ≤ 1 - Real.exp (-k*p.2) := sub_nonneg.mpr hp.2.2.le
  have hu1 : 1 - Real.exp (-k*p.1) ≤ 1 := by linarith [hp.1.1]
  have hu2 : 1 - Real.exp (-k*p.2) ≤ 1 := by linarith [hp.2.1]
  unfold productMutationObservable
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg L) h1) h2)]
  calc
    L^2 * (1 - Real.exp (-k*p.1)) * (1 - Real.exp (-k*p.2)) ≤ L^2 * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu1 (sq_nonneg L)) hu2 h2
        (mul_nonneg (sq_nonneg L) zero_le_one)
    _ = L^2 := by ring

theorem jointLaw_integral_pos_of_ae_pos {f : ℝ × ℝ → ℝ}
    (hi : Integrable f P.pre.jointLaw) (hp : ∀ᵐ p ∂P.pre.jointLaw, 0 < f p) :
    0 < ∫ p, f p ∂P.pre.jointLaw := by
  let := P.jointLaw_probability
  have hn : 0 ≤ᵐ[P.pre.jointLaw] f := hp.mono (fun _ h => h.le)
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp he.symm
  obtain ⟨p, hpos, hzero⟩ := (hp.and hz).exists
  exact (ne_of_gt hpos) hzero

theorem mutationMomentPair_fst_pos {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    0 < (P.mutationMomentPair L k).1 := by
  apply P.jointLaw_integral_pos_of_ae_pos (P.firstMutationObservable_integrable_of_proper hk L)
  filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
  exact mul_pos hL (sub_pos.mpr hp.1.2)

theorem mutationMomentPair_fst_lt {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    (P.mutationMomentPair L k).1 < L := by
  let := P.jointLaw_probability
  have hi := (integrable_const L).sub (P.firstMutationObservable_integrable_of_proper hk L)
  have hp : 0 < ∫ p, (L - firstMutationObservable L k p) ∂P.pre.jointLaw := by
    apply P.jointLaw_integral_pos_of_ae_pos hi
    filter_upwards [] with p
    dsimp [firstMutationObservable]
    nlinarith [mul_pos hL (Real.exp_pos (-k*p.1))]
  rw [integral_sub (integrable_const L) (P.firstMutationObservable_integrable_of_proper hk L)] at hp
  simpa [mutationMomentPair] using (sub_pos.mp hp)

theorem mutationMomentPair_snd_lt_mul_fst {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    (P.mutationMomentPair L k).2 < L * (P.mutationMomentPair L k).1 := by
  have hi1 := P.firstMutationObservable_integrable_of_proper hk L
  have hi2 := P.productMutationObservable_integrable_of_proper hk L
  have hp : 0 < ∫ p, (L * firstMutationObservable L k p -
      productMutationObservable L k p) ∂P.pre.jointLaw := by
    apply P.jointLaw_integral_pos_of_ae_pos ((hi1.const_mul L).sub hi2)
    filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
    have hpos := mul_pos (mul_pos (sq_pos_of_pos hL) (sub_pos.mpr hp.1.2)) hp.2.1
    dsimp [firstMutationObservable, productMutationObservable]
    nlinarith
  rw [integral_sub (hi1.const_mul L) hi2, integral_const_mul] at hp
  exact sub_pos.mp hp

theorem mutationMomentPair_endpoint_bounds {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    0 < (P.mutationMomentPair L k).1 ∧ (P.mutationMomentPair L k).1 < L ∧
      (P.mutationMomentPair L k).2 < L * (P.mutationMomentPair L k).1 :=
  ⟨P.mutationMomentPair_fst_pos hL hk, P.mutationMomentPair_fst_lt hL hk,
    P.mutationMomentPair_snd_lt_mul_fst hL hk⟩

end ProperIntegrablePanModel
end Rhone.Statistics.Identifiability
