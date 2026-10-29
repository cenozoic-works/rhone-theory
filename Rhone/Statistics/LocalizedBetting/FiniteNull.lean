/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.Test

/-! # Fixed-sample localized product null bound; no optional-stopping assertion -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.LocalizedBetting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

def productWealth {N : ℕ} (factor : X → ℝ) (z : Fin N → X) : ℝ := ∏ i, factor (z i)

theorem product_mean_le_one (P : Law X) (N : ℕ) (factor : X → ℝ)
    (hf : ∀ x, 0 ≤ factor x) (hm : rejection P factor ≤ 1) :
    rejection (iid P N) (productWealth factor) ≤ 1 := by
  change rejection (iid P N) (fun z => ∏ i, factor (z i)) ≤ 1
  rw [expectation_product]
  apply Finset.prod_le_one₀
  · intro i _
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))
  · intro i _
    exact hm

theorem product_size (P : Law X) (N : ℕ) (factor : X → ℝ)
    (hf : ∀ x, 0 ≤ factor x) (hm : rejection P factor ≤ 1) :
    probability (iid P N) (fun z => 20 ≤ productWealth factor z) ≤ (1 : ℝ) / 20 := by
  have h := finite_markov (iid P N) (productWealth factor)
    (fun z => Finset.prod_nonneg (fun i _ => hf (z i))) (by norm_num : (0 : ℝ) < 20)
  exact h.trans (div_le_div_of_nonneg_right (product_mean_le_one P N factor hf hm)
    (by norm_num))

theorem localized_size (P : Law X) (N : ℕ) (factor : X → ℝ)
    (localizes : (Fin N → X) → Prop) (near : Prop) (hf : ∀ x, 0 ≤ factor x)
    (hnear : near → rejection P factor ≤ 1)
    (hfar : ¬ near → probability (iid P N) localizes ≤ (1 : ℝ) / 20) :
    probability (iid P N) (fun z => localizes z ∧ 20 ≤ productWealth factor z) ≤
      (1 : ℝ) / 20 := by
  by_cases hn : near
  · exact (probability_mono _ (fun _ h => h.2)).trans (product_size P N factor hf (hnear hn))
  · exact (probability_mono _ (fun _ h => h.1)).trans (hfar hn)

theorem affine_factor_mean (P : Law X) (eta d : ℝ) (z : X → ℝ) :
    rejection P (fun x => 1 + eta * (z x + d)) = 1 + eta * (rejection P z + d) := by
  have h : (∑ x, P.mass x * (1 + eta * (z x + d))) =
      (∑ x, P.mass x) + eta * (∑ x, P.mass x * z x) + d * eta * (∑ x, P.mass x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  change (∑ x, P.mass x * (1 + eta * (z x + d))) = _
  rw [h, P.total]
  simp only [rejection]
  ring

end Rhone.Statistics.LocalizedBetting
