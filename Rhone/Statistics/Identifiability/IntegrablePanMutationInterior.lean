/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanStrictSurvival
public import Rhone.Statistics.Identifiability.IntegrablePanMutationEndpointBounds
public import Rhone.Statistics.Identifiability.WeightedSurvivalTonelli
public import Rhone.Statistics.Identifiability.FourEpochPanLaplaceExactness

/-! # Strict inequalities placing mutation moment pairs in the interior of their domain -/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Rhone.Statistics.Identifiability

namespace ProperIntegrablePanModel
variable (P : ProperIntegrablePanModel)

theorem strict_weighted_survival {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (hwn : ∀ t, 0 < w t) (hwf : ∀ t, w t ≠ ⊤)
    (hfin : (∫⁻ s in Ioi 0, w s * (P.pre.jointLaw.map Prod.fst) (Ioi s)) ≠ ⊤)
    (hJ : Measurable (fun st : ℝ × ℝ => P.pre.jointLaw (Ioi st.1 ×ˢ Ioi st.2))) :
    (∫⁻ s in Ioi 0, w s * (P.pre.jointLaw.map Prod.fst) (Ioi s)) ^ 2 <
      ∫⁻ st, w st.1 * w st.2 * P.pre.jointLaw (Ioi st.1 ×ˢ Ioi st.2)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let ν := (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  let m := fun t => (P.pre.jointLaw.map Prod.fst) (Ioi t)
  let f := fun st : ℝ × ℝ => (w st.1 * m st.1) * (w st.2 * m st.2)
  let g := fun st : ℝ × ℝ => w st.1 * w st.2 * P.pre.jointLaw (Ioi st.1 ×ˢ Ioi st.2)
  have hm : Measurable m :=
    (show Antitone m from fun a b hab => measure_mono (Ioi_subset_Ioi hab)).measurable
  have hf : (∫⁻ st, f st ∂ν) = (∫⁻ s in Ioi 0, w s * m s) ^ 2 := by
    simpa only [pow_two, f, ν, Pi.mul_apply] using lintegral_prod_mul
      (hw.mul hm).aemeasurable (hw.mul hm).aemeasurable
  rw [← hf]
  have hν : ∀ᵐ st ∂ν, 0 < st.1 ∧ 0 < st.2 := by
    dsimp [ν]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hle : f ≤ᵐ[ν] g := by
    filter_upwards [hν] with st hst
    dsimp [f, g, m]
    calc
      _ = (w st.1 * w st.2) * ((P.pre.jointLaw.map Prod.fst) (Ioi st.1) *
          (P.pre.jointLaw.map Prod.fst) (Ioi st.2)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl (P.jointLaw_tail_ge_product hst.1.le hst.2.le)
  obtain ⟨T, hT, hstrict⟩ := P.exists_strict_quadrant_threshold
  let A := Ioo T (T+1) ×ˢ Ioo T (T+1)
  have hA : ν A ≠ 0 := by
    have hsub : Ioo T (T+1) ⊆ Ioi 0 := fun _ h => hT.trans h.1
    dsimp [ν, A]
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr hsub, Real.volume_Ioo]
    norm_num
  apply lintegral_strict_mono_of_ae_le_of_ae_lt_on
    (((hw.comp measurable_fst).mul (hw.comp measurable_snd)).mul hJ).aemeasurable
    (by rw [hf, pow_two]; exact ENNReal.mul_ne_top hfin hfin) hle hA
  filter_upwards [] with st hst
  dsimp [f, g, m]
  have h := ENNReal.mul_lt_mul_right
    (mul_ne_zero (ne_of_gt (hwn st.1)) (ne_of_gt (hwn st.2)))
    (ENNReal.mul_ne_top (hwf st.1) (hwf st.2))
    (hstrict st.1 st.2 hst.1.1.le hst.2.1.le)
  convert h using 1
  ring

theorem mutationMomentPair_sq_fst_lt_snd {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    (P.mutationMomentPair L k).1 ^ 2 < (P.mutationMomentPair L k).2 := by
  let := P.jointLaw_probability
  let w := fun s : ℝ => ENNReal.ofReal (L * k * Real.exp (-k * s))
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hx : ∀ᵐ p ∂P.pre.jointLaw, 0 ≤ p.1 ∧ 0 ≤ p.2 :=
    P.jointLaw_ae_coordinates_pos.mono (fun _ h => ⟨h.1.le, h.2.le⟩)
  have hn1 : 0 ≤ᵐ[P.pre.jointLaw] firstMutationObservable L k := by
    filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
    exact mul_nonneg hL.le (sub_nonneg.mpr hp.1.2.le)
  have hn2 : 0 ≤ᵐ[P.pre.jointLaw] productMutationObservable L k := by
    filter_upwards [P.jointLaw_ae_laplace_bounds hk] with p hp
    exact mul_nonneg (mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hp.1.2.le))
      (sub_nonneg.mpr hp.2.2.le)
  have he1 : ENNReal.ofReal (P.mutationMomentPair L k).1 =
      ∫⁻ s in Ioi 0, w s * (P.pre.jointLaw.map Prod.fst) (Ioi s) := by
    rw [mutationMomentPair, ofReal_integral_eq_lintegral_ofReal
      (P.firstMutationObservable_integrable_of_proper hk L) hn1]
    exact exponentialResponse_lintegral_fst P.pre.jointLaw hL.le hk.le
      (hx.mono (fun _ h => h.1))
  have he2 : ENNReal.ofReal (P.mutationMomentPair L k).2 =
      ∫⁻ st, w st.1 * w st.2 * P.pre.jointLaw (Ioi st.1 ×ˢ Ioi st.2)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [mutationMomentPair, ofReal_integral_eq_lintegral_ofReal
      (P.productMutationObservable_integrable_of_proper hk L) hn2,
      Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact exponentialResponse_lintegral_product P.pre.jointLaw hL.le hk.le hx
  have hstrict := P.strict_weighted_survival hw
    (fun t => ENNReal.ofReal_pos.mpr (mul_pos (mul_pos hL hk) (Real.exp_pos _)))
    (fun _ => ENNReal.ofReal_ne_top) (he1.symm ▸ ENNReal.ofReal_ne_top)
    (measurable_jointSurvival P.pre.jointLaw)
  rw [← he1, ← he2, pow_two,
    ← ENNReal.ofReal_mul (P.mutationMomentPair_fst_pos hL hk).le, ← pow_two] at hstrict
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sq_nonneg _)).mp hstrict

theorem mutationMomentPair_mem_momentDomain {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    P.mutationMomentPair L k ∈ MutationMomentSurjectivity.momentDomain L := by
  exact ⟨P.mutationMomentPair_fst_pos hL hk, P.mutationMomentPair_fst_lt hL hk,
    P.mutationMomentPair_sq_fst_lt_snd hL hk, P.mutationMomentPair_snd_lt_mul_fst hL hk⟩

end ProperIntegrablePanModel

theorem exists_fixedRecomb_mutationMomentPair_iff {L k r : ℝ}
    (hL : 0 < L) (hk : 0 < k) (hr : 0 ≤ r) (y : ℝ × ℝ) :
    (∃ P : ProperIntegrablePanModel,
      P.pre.recomb = (fun _ => r) ∧ P.mutationMomentPair L k = y) ↔
      y ∈ MutationMomentSurjectivity.momentDomain L := by
  constructor
  · rintro ⟨P, _, rfl⟩
    exact P.mutationMomentPair_mem_momentDomain hL hk
  · intro hy
    obtain ⟨ε, δ, M, A, τ, P, _, _, _, _, _, _, hrecomb, _, _, _, heq, _⟩ :=
      FourEpochBackward.exists_fourEpoch_jointLaw_exact hL hr hk hy
    exact ⟨P, hrecomb, heq⟩

theorem exists_mutationMomentPair_iff {L k : ℝ} (hL : 0 < L) (hk : 0 < k)
    (y : ℝ × ℝ) :
    (∃ P : ProperIntegrablePanModel, P.mutationMomentPair L k = y) ↔
      y ∈ MutationMomentSurjectivity.momentDomain L := by
  constructor
  · rintro ⟨P, rfl⟩
    exact P.mutationMomentPair_mem_momentDomain hL hk
  · intro hy
    obtain ⟨P, _, heq⟩ := (exists_fixedRecomb_mutationMomentPair_iff hL hk
      (r := 0) le_rfl y).2 hy
    exact ⟨P, heq⟩

end Rhone.Statistics.Identifiability
