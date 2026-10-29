/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteBlockTesting.Empirical

/-! # Explicit finite iid budget from a supplied uniform finite-alphabet TV gap -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.FiniteBlockTesting
open ThreeSiteRobustness Identifiability.FinitePanelSampling
variable {X : Type*} [Fintype X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]

def frequencyRadius (δ : ℝ) : ℝ := δ / (2 * Fintype.card X)

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem frequency_radius_pos {δ : ℝ} (hδ : 0 < δ) : 0 < frequencyRadius (X := X) δ := by
  unfold frequencyRadius
  positivity

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem frequency_radius_small {δ : ℝ} (hδ : 0 < δ) :
    (Fintype.card X : ℝ) * frequencyRadius (X := X) δ < δ := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold frequencyRadius
  field_simp
  nlinarith

theorem finite_block_source_error {N : ℕ} (P : Measure X) [IsProbabilityMeasure P]
    (hN : 0 < N) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (hbudget : hoeffdingSampleBudget (Fintype.card X) (frequencyRadius (X := X) δ) γ ≤
      (N : ℝ)) :
    (iidLaw P N).real {x | ¬ frequencyRejects P (frequencyRadius (X := X) δ) x} ≤ γ :=
  (frequency_source_failure P hN (frequency_radius_pos hδ).le).trans
    (hoeffding_failure_le Fintype.card_pos (frequency_radius_pos hδ) hγ hbudget)

theorem finite_block_null_size {N : ℕ} (P Q : Measure X) [IsProbabilityMeasure Q]
    (hN : 0 < N) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (hgap : δ ≤ finiteTV P Q)
    (hbudget : hoeffdingSampleBudget (Fintype.card X) (frequencyRadius (X := X) δ) γ ≤
      (N : ℝ)) :
    (iidLaw Q N).real {x | frequencyRejects P (frequencyRadius (X := X) δ) x} ≤ γ :=
  (frequency_null_size P Q hN (frequency_radius_pos hδ).le hgap
    (frequency_radius_small hδ)).trans
    (hoeffding_failure_le Fintype.card_pos (frequency_radius_pos hδ) hγ hbudget)

theorem explicit_budget_suffices (P : Measure X) [IsProbabilityMeasure P]
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) :
    let N := hoeffdingSampleSize (Fintype.card X) (frequencyRadius (X := X) δ) γ
    (iidLaw P N).real {x | ¬ frequencyRejects P (frequencyRadius (X := X) δ) x} ≤ γ ∧
      ∀ Q : Measure X, ∀ (_ : IsProbabilityMeasure Q), δ ≤ finiteTV P Q →
        (iidLaw Q N).real {x | frequencyRejects P (frequencyRadius (X := X) δ) x} ≤ γ := by
  dsimp only
  constructor
  · exact finite_block_source_error P (hoeffdingSampleSize_pos _ _ _) hδ hγ
      (hoeffdingSampleBudget_le_size _ _ _)
  · intro Q hQ hgap
    exact finite_block_null_size P Q (hoeffdingSampleSize_pos _ _ _) hδ hγ hgap
      (hoeffdingSampleBudget_le_size _ _ _)

end Rhone.Statistics.FiniteBlockTesting
