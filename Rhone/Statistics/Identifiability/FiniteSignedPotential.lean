/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteHarmonicSurvival
public import Rhone.Statistics.Identifiability.TripleSurvivalKernel

/-! # A signed row-space potential bounds integrated finite-state survival -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.WeightedExit
open FiniteExponentialJets
variable {n : ℕ}

lemma row_survival_le_one (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) : flowOutput Q i (fun _ => 1) 0 t ≤ 1 := by
  have hn := intervalIntegral.integral_nonneg (μ := volume) ht
    (fun s hs => firstExit_density_nonneg Q hQ hrow i hs.1)
  rw [firstExit_mass_balance] at hn
  linarith

lemma abs_signed_survival_bound (Q : Matrix (Fin n) (Fin n) ℝ) (β : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    |survival Q β t| ≤ ∑ i, |β i| := by
  unfold survival
  calc
    _ ≤ ∑ i, |β i * flowOutput Q i (fun _ => 1) 0 t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |β i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (survival_nonneg Q hQ i ht)]
      exact mul_le_of_le_one_right (abs_nonneg _) (row_survival_le_one Q hQ hrow i ht)

lemma signed_survival_derivative (Q : Matrix (Fin n) (Fin n) ℝ) (β α : Fin n → ℝ)
    (hβ : β ᵥ* Q = α) (t : ℝ) : HasDerivAt (survival Q β) (survival Q α t) t := by
  have hd := (scalarOutputLinear β (fun _ => 1)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' Q t)
  convert! hd using 1
  · ext s
    rw [survival_eq_matrix]
    rfl
  · change survival Q α t = dotProduct β ((Q * NormedSpace.exp (t • Q)) *ᵥ (fun _ => 1))
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, hβ, survival_eq_matrix]

lemma integrated_survival_bound (Q : Matrix (Fin n) (Fin n) ℝ) (β α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (hβ : β ᵥ* Q = α) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, survival Q α s) ≤ 2 * ∑ i, |β i| := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => signed_survival_derivative Q β α hβ s)
    ((survival_contDiff Q α).continuous.intervalIntegrable 0 t)
  rw [he]
  have htB := abs_signed_survival_bound Q β hQ hrow ht
  have h0B := abs_signed_survival_bound Q β hQ hrow (le_refl (0 : ℝ))
  have h1 := le_abs_self (survival Q β t)
  have h2 := neg_abs_le (survival Q β 0)
  linarith

lemma survival_antitoneOn (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (hα : ∀ i, 0 ≤ α i) :
    AntitoneOn (survival Q α) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t _ => (survival_derivative Q α t).continuousAt.continuousWithinAt)
    (fun t _ => (survival_derivative Q α t).hasDerivWithinAt)
  intro t ht
  exact neg_nonpos.mpr (density_nonnegative Q α hQ hrow hα (interior_subset ht))

lemma survival_le_signed_potential_div (Q : Matrix (Fin n) (Fin n) ℝ) (β α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (hα : ∀ i, 0 ≤ α i)
    (hβ : β ᵥ* Q = α) {t : ℝ} (ht : 0 < t) :
    survival Q α t ≤ (2 * ∑ i, |β i|) / t := by
  have hm := intervalIntegral.integral_mono_on (μ := volume) ht.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => survival Q α t) volume 0 t)
    ((survival_contDiff Q α).continuous.intervalIntegrable 0 t)
    (fun s hs => survival_antitoneOn Q α hQ hrow hα hs.1 ht.le hs.2)
  have hl : t * survival Q α t ≤ ∫ s in 0..t, survival Q α s := by
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hm
  apply (le_div_iff₀ ht).mpr
  have hu := integrated_survival_bound Q β α hQ hrow hβ ht.le
  nlinarith

lemma survival_tendsto_zero_of_rowSpace (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (hα : ∀ i, 0 ≤ α i)
    (hspace : ∃ β : Fin n → ℝ, β ᵥ* Q = α) : Tendsto (survival Q α) atTop (𝓝 0) := by
  obtain ⟨β, hβ⟩ := hspace
  have hlim : Tendsto (fun t : ℝ => (2 * ∑ i, |β i|) / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := (2 * ∑ i, |β i|))).mul tendsto_inv_atTop_zero
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_nonnegative Q α hQ hα ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact survival_le_signed_potential_div Q β α hQ hrow hα hβ ht

end Rhone.Statistics.Identifiability.WeightedExit
