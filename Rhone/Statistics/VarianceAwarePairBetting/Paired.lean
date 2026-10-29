/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.Power
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting

/-! # Binary contrast and independent-pair instantiation of the calibrated bet -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget DependentPairedTest LinkedAgreementPower
variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem binary_difference_bound {F G : X → ℝ} (hF : Binary F) (hG : Binary G) (x : X) :
    |F x - G x| ≤ 1 := by
  rcases hF x with hF | hF <;> rcases hG x with hG | hG <;> norm_num [hF, hG]

theorem binary_source_power (P : Law X) (N : ℕ) {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) (hδ : 0 < contrastMean P F G)
    (hbudget : 128 * discordance P F G ≤ N * contrastMean P F G ^ 2) :
    (19 : ℝ) / 20 ≤ probability (iid P N)
      (Rejects (tuning (contrastMean P F G) (discordance P F G)) (fun x => F x - G x)) := by
  have hδr : contrastMean P F G ≤ discordance P F G :=
    (le_abs_self _).trans (abs_mean_le_discordance P hF hG)
  have hr := hδ.trans_le hδr
  apply source_power P N _ hδ hδr (binary_difference_bound hF hG) rfl rfl
  unfold signal
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hr).mpr hbudget

def pairedContrast (f : X → ℝ) (x : X × X) : ℝ := f x.1 - f x.2

def pairedTuning (P Q : Law X) (f : X → ℝ) : ℝ :=
  tuning (rejection P f - rejection Q f)
    (rejection P f + rejection Q f - 2 * rejection P f * rejection Q f)

theorem pair_source_power (P Q : Law X) (f : X → ℝ) (hf : Binary f) (N : ℕ)
    (hδ : rejection Q f < rejection P f)
    (hbudget : 128 * (rejection P f + rejection Q f - 2 * rejection P f * rejection Q f) ≤
      N * (rejection P f - rejection Q f) ^ 2) :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair P Q) N)
      (Rejects (pairedTuning P Q f) (pairedContrast f)) := by
  have hd := coupling_contrast_mean (independentPair P Q) P Q (independent_coupling P Q) f f
  have hr := independent_discordance P Q hf
  have h := binary_source_power (independentPair P Q) N (fun x => hf x.1) (fun x => hf x.2)
    (by rw [hd]; exact sub_pos.mpr hδ) (by rw [hd, hr]; exact hbudget)
  change (19 : ℝ) / 20 ≤ probability (iid (independentPair P Q) N)
    (Rejects (tuning (rejection P f - rejection Q f)
      (rejection P f + rejection Q f - 2 * rejection P f * rejection Q f))
      (fun x => f x.1 - f x.2))
  simpa only [hd, hr] using h

theorem common_pair_size (P : Law X) (f : X → ℝ) (hf : Binary f) (N : ℕ)
    {lam : ℝ} (hlam : |lam| ≤ 1 / 3) :
    probability (iid (independentPair P P) N) (Rejects lam (pairedContrast f)) ≤
      (1 : ℝ) / 20 := by
  apply common_size _ N hlam _ (binary_difference_bound (fun x => hf x.1) (fun x => hf x.2))
  change contrastMean (independentPair P P) (fun x => f x.1) (fun x => f x.2) = 0
  rw [coupling_contrast_mean _ P P (independent_coupling P P), sub_self]

theorem paired_tuning_bound (P Q : Law X) (f : X → ℝ) (hf : Binary f)
    (hδ : rejection Q f < rejection P f) : |pairedTuning P Q f| ≤ 1 / 3 := by
  have hd := coupling_contrast_mean (independentPair P Q) P Q (independent_coupling P Q) f f
  have hr := independent_discordance P Q hf
  have hh := abs_mean_le_discordance (independentPair P Q) (fun x => hf x.1) (fun x => hf x.2)
  rw [hd, hr, abs_of_pos (sub_pos.mpr hδ)] at hh
  rw [pairedTuning, abs_of_pos (tuning_bounds (sub_pos.mpr hδ) hh).1]
  exact (tuning_bounds (sub_pos.mpr hδ) hh).2

end Rhone.Statistics.VarianceAwarePairBetting
