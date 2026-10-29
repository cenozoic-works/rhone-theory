/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.NullClosureTesting.ProductBound

/-! # Finite-N randomized testing obstruction from TV null closure -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.NullClosureTesting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

noncomputable def continuityFactor (X : Type*) [Fintype X] (N : ℕ) : ℝ :=
  (N : ℝ) * Fintype.card (Fin N → X) + 1

theorem continuity_factor_pos (N : ℕ) : 0 < continuityFactor X N := by
  unfold continuityFactor
  positivity

theorem iid_tv_continuity_bound (P Q : Law X) (N : ℕ) :
    totalVariation (iid P N) (iid Q N) ≤ continuityFactor X N * totalVariation P Q := by
  have htv : 0 ≤ totalVariation P Q := by
    unfold totalVariation
    positivity
  have hp (x : Fin N → X) :
      |(iid P N).mass x - (iid Q N).mass x| ≤ (N : ℝ) * (2 * totalVariation P Q) := by
    have h := bounded_product_difference Finset.univ (fun i => P.mass (x i))
      (fun i => Q.mass (x i)) (fun i _ => ⟨P.nonneg _, mass_le_one P _⟩)
      (fun i _ => ⟨Q.nonneg _, mass_le_one Q _⟩)
    apply h.trans
    calc
      ∑ i : Fin N, |P.mass (x i) - Q.mass (x i)| ≤
          ∑ _i : Fin N, 2 * totalVariation P Q :=
        Finset.sum_le_sum fun i _ => atom_difference_le P Q (x i)
      _ = _ := by simp
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hp x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  unfold totalVariation at hsum htv ⊢
  unfold continuityFactor
  nlinarith

theorem approximable_test_power_le_size (P : Law X) (null : Set (Law X)) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α : ℝ}
    (hsize : ∀ Q ∈ null, rejection (iid Q N) φ ≤ α)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Q ∈ null, totalVariation P Q < ε) :
    rejection (iid P N) φ ≤ α := by
  by_contra hn
  have hd : 0 < rejection (iid P N) φ - α := sub_pos.mpr (lt_of_not_ge hn)
  have hc := continuity_factor_pos (X := X) N
  obtain ⟨Q, hQ, hdist⟩ := happrox
    ((rejection (iid P N) φ - α) / (2 * continuityFactor X N)) (by positivity)
  have hdiff := (abs_le.mp (rejection_difference_le (iid P N) (iid Q N) φ hφ)).2
  have hprod := iid_tv_continuity_bound P Q N
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2 * continuityFactor X N)).mp hdist
  have hs := hsize Q hQ
  nlinarith

theorem test_advantage_implies_gap (P : Law X) (null : Set (Law X)) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α : ℝ}
    (hsize : ∀ Q ∈ null, rejection (iid Q N) φ ≤ α)
    (hpower : α < rejection (iid P N) φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q ∈ null, ε ≤ totalVariation P Q := by
  by_contra hn
  push Not at hn
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ Q ∈ null, totalVariation P Q < ε := by
    intro ε hε
    exact hn ε hε
  exact (not_lt_of_ge (approximable_test_power_le_size P null N φ hφ hsize happrox)) hpower

end Rhone.Statistics.NullClosureTesting
