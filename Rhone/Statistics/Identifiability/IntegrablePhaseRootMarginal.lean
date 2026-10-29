/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhaseHistory
public import Rhone.Statistics.Identifiability.TwoEventFluxLaw

/-! # The root marginal of a general locally-L1 two-stage history -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix ENNReal
namespace Rhone.Statistics.Identifiability.IntegrablePhase.History
variable {n m : ℕ}

lemma column_integrable (M : History n m) (t : ℝ) :
    IntervalIntegrable (fun s => M.density (s,t)) volume 0 t := by
  simp_rw [M.density_matrix]
  convert! IntervalIntegrable.sum Finset.univ (fun i _ =>
    (post_payoff_intervalIntegrable M.N M.A M.B M.F M.N_integrable M.A_integrable
      M.B_integrable M.pre_pre M.post_pre M.pre_post M.post_post 0 t i
      (exitRate (M.B t))).const_mul (M.α i)) using 1
  funext s
  simp only [Finset.sum_apply]

lemma column_integral_ae (M : History n m) :
    ∀ᵐ t, 0 ≤ t → (∫ s in 0..t, M.density (s,t)) =
      IntegrableWeightedExit.density M.N M.γ 0 t := by
  filter_upwards [M.exit_pre, M.exit_post] with t hpre hpost ht
  simp_rw [M.density_matrix]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (post_payoff_intervalIntegrable M.N M.A M.B M.F M.N_integrable M.A_integrable
      M.B_integrable M.pre_pre M.post_pre M.pre_post M.post_post 0 t i
      (exitRate (M.B t))).const_mul (M.α i))]
  simp_rw [intervalIntegral.integral_const_mul,
    post_payoff_integral M.N M.A M.B M.F M.N_integrable M.A_integrable
      M.B_integrable M.pre_pre M.post_pre M.pre_post M.post_post]
  rw [IntegrableWeightedExit.density, IntegrableWeightedExit.row, ← dotProduct_mulVec]
  simp only [dotProduct, Matrix.mulVec, γ, Fin.sum_univ_add, Fin.addCases_left,
    Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero,
    hpre ht, hpost ht, mul_zero, zero_add, postRow]

lemma column_nonnegative_ae (M : History n m) {t : ℝ}
    (hB : ∀ i, (∑ j, M.B t i j) ≤ 0) :
    ∀ᵐ s ∂volume.restrict (Ioo 0 t), 0 ≤ M.density (s,t) := by
  filter_upwards [M.F_nonnegative.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioo] with s hF hs
  exact M.density_nonnegative_at hs.1.le hs.2.le (hF hs.1.le) hB

lemma root_marginal (M : History n m) :
    M.law.map Prod.snd = IntegrableWeightedExit.law M.N M.γ 0 := by
  rw [law, triangular_map_snd_positive_ae _ M.density_aemeasurable.restrict]
  apply withDensity_congr_ae
  filter_upwards [M.column_integral_ae.filter_mono (ae_mono Measure.restrict_le_self),
    M.B_rows.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t hcol hB ht
  rw [← hcol ht.le]
  exact (TwoEventFluxLaw.ofReal_columnIntegral M.density ht.le (M.column_integrable t)
    (M.column_nonnegative_ae (hB ht.le))).symm

lemma law_mass_le_one (M : History n m) : M.law univ ≤ 1 := by
  have he : IntegrableWeightedExit.law M.N M.γ 0 univ = M.law univ := by
    rw [← M.root_marginal, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
  rw [← he]
  have h := IntegrableWeightedExit.law_mass_le_initial M.N M.γ M.N_integrable
    M.N_metzler M.N_rows M.γ_nonnegative (le_refl (0 : ℝ))
  simpa only [M.γ_sum, ENNReal.ofReal_one] using h

lemma law_isFinite (M : History n m) : IsFiniteMeasure M.law :=
  ⟨M.law_mass_le_one.trans_lt (by simp)⟩

end Rhone.Statistics.Identifiability.IntegrablePhase.History
