/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PooledPairPowerIndex.ScanNull
public import Rhone.Statistics.PooledPairPowerIndex.Index
public import Mathlib.Data.Finset.Max

/-! # Full-category sufficient power index Nt>=80M^2 -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest LinkedAgreementPower
variable {X : Type*} [Fintype X] [Nonempty X]

omit [Nonempty X] in
theorem indicator_mean (P : Law X) (b : X) : rejection P (indicator b) = P.mass b := by
  classical
  simp [rejection, indicator]

theorem exists_informative_category (P Q : Law X) (N : ℕ)
    (hbudget : 80 * (Fintype.card X : ℝ) ^ 2 ≤ N * pooledIndex P Q) :
    ∃ b : X, P.mass b ≠ Q.mass b ∧
      160 * Fintype.card X * (P.mass b + Q.mass b) ≤ N * (P.mass b - Q.mass b) ^ 2 := by
  classical
  have hM : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ht : 0 < pooledIndex P Q := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hN (le_of_not_gt hn)
    nlinarith [sq_pos_of_pos hM]
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ (categoryIndex P Q) Finset.univ_nonempty
  have hs : pooledIndex P Q ≤ Fintype.card X * categoryIndex P Q b := by
    have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hb x (Finset.mem_univ x))
    simpa only [pooledIndex, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hib : 0 < categoryIndex P Q b := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hM.le (le_of_not_gt hn)
    linarith
  have hne : P.mass b ≠ Q.mass b := by
    intro he
    have hz := (category_index_zero_iff P Q b).mpr he
    linarith
  have hsum : 0 < P.mass b + Q.mass b := by
    have hp := P.nonneg b
    have hq := Q.nonneg b
    by_contra hn
    have he : P.mass b = Q.mass b := by linarith
    exact hne he
  have hNidx : 80 * (Fintype.card X : ℝ) ≤ N * categoryIndex P Q b := by
    apply (mul_le_mul_iff_right₀ hM).mp
    have hh := mul_le_mul_of_nonneg_left hs hN
    nlinarith
  have he : (P.mass b - Q.mass b) ^ 2 =
      2 * (P.mass b + Q.mass b) * categoryIndex P Q b := by
    unfold categoryIndex
    field_simp
  refine ⟨b, hne, ?_⟩
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hNidx (by positivity : 0 ≤ 2 * (P.mass b + Q.mass b))
  nlinarith

theorem scan_source_power (P Q : Law X) (N : ℕ)
    (hbudget : 80 * (Fintype.card X : ℝ) ^ 2 ≤ N * pooledIndex P Q) :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair P Q) N) ScanRejects := by
  obtain ⟨b, hne, hb⟩ := exists_informative_category P Q N hbudget
  have hM : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hp := iid_binary_power_at (independentPair P Q) N
    (by nlinarith : (20 : ℝ) ≤ 20 * Fintype.card X)
    (fun x => indicator_binary b x.1) (fun x => indicator_binary b x.2)
  have hm : contrastMean (independentPair P Q) (fun x => indicator b x.1)
      (fun x => indicator b x.2) = P.mass b - Q.mass b := by
    rw [coupling_contrast_mean _ P Q (independent_coupling P Q), indicator_mean, indicator_mean]
  have hd : discordance (independentPair P Q) (fun x => indicator b x.1)
      (fun x => indicator b x.2) = P.mass b + Q.mass b - 2 * P.mass b * Q.mass b := by
    rw [independent_discordance _ _ (indicator_binary b), indicator_mean, indicator_mean]
  have hpower := hp (by rw [hm]; exact sub_ne_zero.mpr hne) (by
    rw [hm, hd]
    have hprod := mul_nonneg (P.nonneg b) (Q.nonneg b)
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    nlinarith [mul_nonneg hcard hprod])
  apply hpower.trans (probability_mono _ _)
  intro z hz
  exact ⟨b, hz⟩

end Rhone.Statistics.PooledPairPowerIndex
