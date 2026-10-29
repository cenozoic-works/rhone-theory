/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.ScaledAdjugate

/-! # The scaled cleared chain satisfies the top-coefficient recurrence -/

@[expose] public section

namespace Rhone.Probability.ChainDenominator

open Polynomial DiagonalChain Analysis.RareAlleleHierarchy RareAlleleHierarchy

def chainDegree (k t : ℕ) : ℕ := Nat.choose k 2 + t - 1

theorem clearedChain_scaled (A B : ℤ) (k : ℕ) (hk : 1 ≤ k) : ∀ t : ℕ, t ≤ k →
    (clearedChain (C A * X) (C B * X) k t).natDegree ≤ chainDegree k t ∧
    (clearedChain (C A * X) (C B * X) k t).coeff (chainDegree k t) = topG A B k t := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro t ht
    interval_cases t <;> simp [chainDegree, varthetaOne]
  | succ n hn ih =>
    intro t ht
    let f : ℕ → ℤ[X] := fun u => adjD (n + 1) (C A * X) (C B * X) t u *
      diagSource (clearedChain (C A * X) (C B * X) n) u
    have hs : clearedChain (C A * X) (C B * X) (n + 1) t =
        ∑ u ∈ Finset.range (n + 2), f u := by
      rw [clearedChain_step _ _ (by omega), clearedStep_eq_range]
      rfl
    have hz (u : ℕ) (hu : u < 2) : f u = 0 := by
      have h : u * (u - 1) = 0 := by interval_cases u <;> rfl
      change adjD _ _ _ _ _ * (((u * (u - 1) : ℕ) : ℤ[X]) * _) = 0
      rw [h, Nat.cast_zero, zero_mul, mul_zero]
    have hd (u : ℕ) (hu : 2 ≤ u) (huk : u ≤ n + 1) :
        (diagSource (clearedChain (C A * X) (C B * X) n) u).natDegree ≤
          chainDegree n (u - 1) := by
      unfold diagSource
      refine natDegree_mul_le.trans ?_
      rw [natDegree_natCast, Nat.zero_add]
      exact (ih (u - 1) (by omega)).1
    have htop (u : ℕ) (hu : 2 ≤ u) (huk : u ≤ n + 1) :
        (diagSource (clearedChain (C A * X) (C B * X) n) u).coeff
          (chainDegree n (u - 1)) = ((u : ℤ) * ((u : ℤ) - 1)) * topG A B n (u - 1) := by
      unfold diagSource
      rw [← map_natCast C, coeff_C_mul, (ih (u - 1) (by omega)).2]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ u), Nat.cast_one]
    have hdeg (u : ℕ) (hu : u ∈ Finset.range (n + 2)) :
        (f u).natDegree ≤ chainDegree (n + 1) t := by
      have huk : u ≤ n + 1 := by rw [Finset.mem_range] at hu; omega
      by_cases hu2 : 2 ≤ u
      · have hmul := natDegree_mul_le (p := adjD (n + 1) (C A * X) (C B * X) t u)
          (q := diagSource (clearedChain (C A * X) (C B * X) n) u)
        have hsrc := hd u hu2 huk
        rcases le_total t u with htu | hut
        · have ha := adj_scaled_upper_degree A B (n + 1) t u htu huk
          dsimp [f]
          dsimp [chainDegree] at *
          rw [choose_two_succ] at ⊢
          omega
        · have ha := adj_scaled_lower_degree A B (n + 1) t u hut ht
          dsimp [f]
          dsimp [chainDegree] at *
          rw [choose_two_succ] at ⊢
          omega
      · rw [hz u (by omega), natDegree_zero]
        exact Nat.zero_le _
    refine ⟨by rw [hs]; exact natDegree_sum_le_of_forall_le _ _ hdeg, ?_⟩
    have hbelow (u : ℕ) (hu : u ∈ Finset.range (n + 2)) (hut : u < t) :
        (f u).coeff (chainDegree (n + 1) t) = 0 := by
      by_cases hu2 : 2 ≤ u
      · have huk : u ≤ n + 1 := by rw [Finset.mem_range] at hu; omega
        have hmul := natDegree_mul_le (p := adjD (n + 1) (C A * X) (C B * X) t u)
          (q := diagSource (clearedChain (C A * X) (C B * X) n) u)
        have hsrc := hd u hu2 huk
        have ha := adj_scaled_lower_degree A B (n + 1) t u (by omega) ht
        apply coeff_eq_zero_of_natDegree_lt
        dsimp [f]
        dsimp [chainDegree] at *
        rw [choose_two_succ] at ⊢
        omega
      · rw [hz u (by omega), coeff_zero]
    have habove (u : ℕ) (hu : u ∈ Finset.Icc (max t 2) (n + 1)) :
        (f u).coeff (chainDegree (n + 1) t) =
          (∏ x ∈ Finset.range t, Lam A B (n + 1) x) *
          (2 ^ (u - t) * (∏ s ∈ Finset.Ico t u, (((n + 1 : ℕ) : ℤ) - (s : ℤ)) ^ 2) *
          ((u : ℤ) * ((u : ℤ) - 1)) *
          (∏ x ∈ Finset.Ico (u + 1) (n + 2), Lam A B (n + 1) x) *
          topG A B n (u - 1)) := by
      obtain ⟨hlo, huk⟩ := Finset.mem_Icc.mp hu
      have htu : t ≤ u := (le_max_left t 2).trans hlo
      have hu2 : 2 ≤ u := (le_max_right t 2).trans hlo
      have heq : chainDegree (n + 1) t = t + (n + 1 - u) + chainDegree n (u - 1) := by
        simp only [chainDegree, choose_two_succ]
        omega
      dsimp only [f]
      rw [heq, coeff_mul_add_eq_of_natDegree_le
        (adj_scaled_upper_degree A B (n + 1) t u htu huk) (hd u hu2 huk),
        adj_scaled_upper_coeff A B (n + 1) t u htu huk, htop u hu2 huk,
        upperWeight_eq (n + 1) t u huk]
      ring
    rw [hs, finsetSum_coeff]
    have hsub : Finset.Icc (max t 2) (n + 1) ⊆ Finset.range (n + 2) := by
      intro u hu
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    rw [← Finset.sum_subset hsub (by
      intro u hu hnot
      by_cases hut : u < t
      · exact hbelow u hu hut
      · have hu2 : u < 2 := by
          simp only [Finset.mem_Icc, Finset.mem_range] at *
          omega
        rw [hz u hu2, coeff_zero])]
    rw [Finset.sum_congr rfl habove, ← Finset.mul_sum]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl

theorem W_scaled_natDegree_le (A B : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (W k (C A * X) (C B * X)).natDegree ≤ Nat.choose k 2 - 1 := by
  simpa only [W, chainDegree, Nat.add_zero] using
    (clearedChain_scaled A B k hk 0 (Nat.zero_le k)).1

theorem W_scaled_coeff (A B : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (W k (C A * X) (C B * X)).coeff (Nat.choose k 2 - 1) = topG A B k 0 := by
  simpa only [W, chainDegree, Nat.add_zero] using
    (clearedChain_scaled A B k hk 0 (Nat.zero_le k)).2

theorem W_scaled_top_vanishes (k : ℕ) (hk : 3 ≤ k) :
    (W k (C (ptA k) * X) (C (ptB k) * X)).coeff (Nat.choose k 2 - 1) = 0 := by
  rw [W_scaled_coeff _ _ k (by omega)]
  exact topG_vanishes_at_km1 hk

theorem W_scaled_top_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < (W k (C (qtA k) * X) (C (qtB k) * X)).coeff (Nat.choose k 2 - 1) := by
  rw [W_scaled_coeff _ _ k (by omega)]
  exact topG_pos_at_k hk

theorem W_scaled_natDegree_at_k (k : ℕ) (hk : 2 ≤ k) :
    (W k (C (qtA k) * X) (C (qtB k) * X)).natDegree = Nat.choose k 2 - 1 := by
  exact le_antisymm (W_scaled_natDegree_le _ _ k (by omega))
    (le_natDegree_of_ne_zero (W_scaled_top_pos k hk).ne')

end Rhone.Probability.ChainDenominator
