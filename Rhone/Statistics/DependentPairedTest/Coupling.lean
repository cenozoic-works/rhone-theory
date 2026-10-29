/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Ternary
public import Rhone.Statistics.DependentPairedTest.Power
public import Mathlib.Data.Fintype.BigOperators

/-! # Exact-marginal coupling bridges -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X Y : Type*} [Fintype X] [Fintype Y]

def IsCoupling (R : Law (X × Y)) (P : Law X) (Q : Law Y) : Prop :=
  (∀ x, ∑ y, R.mass (x, y) = P.mass x) ∧ (∀ y, ∑ x, R.mass (x, y) = Q.mass y)

theorem coupling_first_mean (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) (f : X → ℝ) :
    rejection R (fun z => f z.1) = rejection P f := by
  unfold rejection
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, h.1]

theorem coupling_second_mean (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) (g : Y → ℝ) :
    rejection R (fun z => g z.2) = rejection Q g := by
  unfold rejection
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul, h.2]

theorem coupling_contrast_mean (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) (f : X → ℝ) (g : Y → ℝ) :
    contrastMean R (fun z => f z.1) (fun z => g z.2) = rejection P f - rejection Q g := by
  rw [contrast_mean, coupling_first_mean R P Q h, coupling_second_mean R P Q h]

theorem coupling_null_size (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) {f : X → ℝ} {g : Y → ℝ}
    (hf : Binary f) (hg : Binary g) (hmean : rejection P f = rejection Q g) (N : ℕ) :
    probability (iid R N) (fun z => Rejects (fun i => f (z i).1 - g (z i).2)) ≤
      (1 : ℝ) / 20 := by
  apply iid_binary_null_size R N (fun z => hf z.1) (fun z => hg z.2)
  rw [coupling_first_mean R P Q h, coupling_second_mean R P Q h, hmean]

theorem coupling_worst_discordance_power (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) {f : X → ℝ} {g : Y → ℝ}
    (hf : Binary f) (hg : Binary g) (N : ℕ)
    (hbudget : 160 ≤ N * (rejection P f - rejection Q g) ^ 2) :
    (19 : ℝ) / 20 ≤ probability (iid R N)
      (fun z => Rejects (fun i => f (z i).1 - g (z i).2)) := by
  have hd := discordance_le_one R (fun z => hf z.1) (fun z => hg z.2)
  apply iid_binary_power R N (fun z => hf z.1) (fun z => hg z.2)
  · rw [coupling_contrast_mean R P Q h]
    intro hz
    rw [hz] at hbudget
    norm_num at hbudget
  · rw [coupling_contrast_mean R P Q h]
    linarith

end Rhone.Statistics.DependentPairedTest
