/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RankFactorization

/-! # A marginal-free non-factorization theorem for the upper density -/

@[expose] public section

open Set
namespace Rhone.Statistics.Identifiability

noncomputable def densityDeterminant (k : Nat) (c q r s₁ s₂ t₁ t₂ : ℝ) : ℝ :=
  upperDensity k c q r s₁ t₁ * upperDensity k c q r s₂ t₂ -
    upperDensity k c q r s₁ t₂ * upperDensity k c q r s₂ t₁

theorem densityDeterminant_nonzero (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ∃ s₁ ∈ Ioo (0 : ℝ) 1, ∃ s₂ ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Icc (2 : ℝ) 3,
      densityDeterminant k c q r s₁ s₂ 2 t ≠ 0 := by
  obtain ⟨s₁, hs₁, s₂, hs₂, hrow⟩ := backward_rank_two k hc hq hr
  have hs₁ne : s₁ ≠ 0 := by intro h; simp [h] at hrow
  have hs₂ne : s₂ ≠ 0 := by intro h; simp [h] at hrow
  obtain ⟨t, ht, hcol⟩ := column_rank_two_of_wronskian _ _ (show (2 : ℝ) < 3 by norm_num)
    (forwardDensity_hasDerivAt k c q 0 2) (forwardDensity_hasDerivAt k c q 1 2)
    (forward_wronskian_ne_zero k hc.ne' hq.ne' 2)
  refine ⟨s₁, ⟨lt_of_le_of_ne hs₁.1 hs₁ne.symm, by linarith [hs₁.2]⟩,
    s₂, ⟨lt_of_le_of_ne hs₂.1 hs₂ne.symm, by linarith [hs₂.2]⟩, t, ht, ?_⟩
  unfold densityDeterminant
  simp only [upperDensity_factorization]
  rw [rank_product_determinant]
  exact mul_ne_zero hrow hcol

theorem no_pointwise_rank_one_density (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ ∃ a b : ℝ → ℝ, ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioi (1 : ℝ),
      upperDensity k c q r s t = a s * b t := by
  rintro ⟨a,b,h⟩
  obtain ⟨s₁,hs₁,s₂,hs₂,t,ht,hne⟩ := densityDeterminant_nonzero k hc hq hr
  apply hne
  unfold densityDeterminant
  rw [h s₁ hs₁ 2 (by norm_num), h s₂ hs₂ t (by change 1 < t; linarith [ht.1]),
    h s₁ hs₁ t (by change 1 < t; linarith [ht.1]), h s₂ hs₂ 2 (by norm_num)]
  ring

end Rhone.Statistics.Identifiability
