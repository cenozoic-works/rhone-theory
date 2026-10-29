/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.TwoSiteStationary.Features

/-! # The leading-coefficient rigidity step in the all-degree atomic-rank argument -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.AtomicRank

def growth (q : ℕ) : ℝ := ((q : ℝ) + 2) / ((q : ℝ) + 1)

lemma growth_gt_one (q : ℕ) : 1 < growth q := by
  unfold growth
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < q + 1)).mpr
  linarith

lemma growth_product_gt_one (p q : ℕ) : 1 < growth p * growth q := by
  have hp := growth_gt_one p
  have hq := growth_gt_one q
  nlinarith

lemma transpose_coefficients_zero (p q : ℕ) {a b : ℝ}
    (h1 : b = growth q * a) (h2 : a = growth p * b) : a = 0 ∧ b = 0 := by
  have he : (1 - growth p * growth q) * a = 0 := by
    rw [h1] at h2
    linear_combination h2
  have hn : 1 - growth p * growth q ≠ 0 := by
    have h := growth_product_gt_one p q
    linarith
  have ha := (mul_eq_zero.mp he).resolve_left hn
  exact ⟨ha, by rw [h1, ha, mul_zero]⟩

theorem homogeneous_coefficients_shape (r : ℕ) (hr : 0 < r)
    (c : ℕ → ℕ → ℝ)
    (h : ∀ p q : ℕ, p + q = r → 0 < p → c q p = growth q * c p q) :
    (∀ p q : ℕ, p + q = r → 0 < p → 0 < q → c p q = 0) ∧
      c 0 r = 2 * c r 0 := by
  constructor
  · intro p q hpq hp hq
    exact (transpose_coefficients_zero p q (h p q hpq hp)
      (h q p (by omega) hq)).1
  · have he := h r 0 (by omega) hr
    norm_num [growth] at he
    exact he

end Rhone.Statistics.AtomicRank
