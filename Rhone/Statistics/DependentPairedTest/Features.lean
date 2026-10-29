/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependenceBudget.Transfer

/-! # Binary-feature moments for an arbitrary whole-replicate law -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

def Binary (F : X → ℝ) : Prop := ∀ x, F x = 0 ∨ F x = 1

noncomputable def contrastMean (P : Law X) (F G : X → ℝ) : ℝ :=
  ∑ x, P.mass x * (F x - G x)

noncomputable def discordance (P : Law X) (F G : X → ℝ) : ℝ :=
  ∑ x, P.mass x * (F x - G x)^2

theorem contrast_mean (P : Law X) (F G : X → ℝ) :
    contrastMean P F G = rejection P F - rejection P G := by
  simp [contrastMean, rejection, mul_sub, Finset.sum_sub_distrib]

theorem discordance_identity (P : Law X) {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) :
    discordance P F G = rejection P F + rejection P G -
      2 * rejection P (fun x => F x * G x) := by
  unfold discordance rejection
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases hF x with hf | hf <;> rcases hG x with hg | hg <;> simp [hf, hg]
  ring1

theorem discordance_nonneg (P : Law X) (F G : X → ℝ) :
    0 ≤ discordance P F G :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (sq_nonneg _))

theorem discordance_le_one (P : Law X) {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) : discordance P F G ≤ 1 := by
  rw [← P.total]
  apply Finset.sum_le_sum
  intro x _
  rcases hF x with hf | hf <;> rcases hG x with hg | hg <;>
    simp [hf, hg, P.nonneg x]

theorem abs_mean_le_discordance (P : Law X) {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) : |contrastMean P F G| ≤ discordance P F G := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [abs_mul, abs_of_nonneg (P.nonneg x)]
  apply mul_le_mul_of_nonneg_left _ (P.nonneg x)
  rcases hF x with hf | hf <;> rcases hG x with hg | hg <;> simp [hf, hg]

end Rhone.Statistics.DependentPairedTest
