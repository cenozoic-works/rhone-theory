/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsVarianceCoeff

/-!
# Coefficients of the covariance of two classes of the site frequency spectrum

Source: fu1995, eq. (2)–(5), pp. 174–175. -/

@[expose] public section
namespace Rhone.Statistics

noncomputable def fuNestWeight (m a c : ℕ) : ℝ :=
  if 1 ≤ a ∧ 1 ≤ c ∧ a + c < m then -fuPhi m a else 0

theorem fuNestWeight_of_lt {m a c : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (h : a + c < m) :
    fuNestWeight m a c = -fuPhi m a := ite_eq_left ⟨ha, hc, h⟩

theorem fuNestWeight_of_not {m a c : ℕ} (h : ¬ (1 ≤ a ∧ 1 ≤ c ∧ a + c < m)) :
    fuNestWeight m a c = 0 := ite_eq_right h

theorem fuNestWeight_step {k a c : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hac : a + c < k) :
    ((a : ℝ) - 1) * fuNestWeight (k - 1) (a - 1) c +
        ((c : ℝ) - 1) * fuNestWeight (k - 1) a (c - 1) +
        ((k : ℝ) - a - c - 1) * fuNestWeight (k - 1) a c =
      ((k : ℝ) - 1) * fuNestWeight k a c - if a = 1 then 4 / (k : ℝ) else 0 := by
  have h2 : ((c : ℝ) - 1) * fuNestWeight (k - 1) a (c - 1) =
      ((c : ℝ) - 1) * (-fuPhi (k - 1) a) := by
    rcases Nat.eq_or_lt_of_le hc with rfl | hc2
    · rw [Nat.cast_one, sub_self, zero_mul, zero_mul]
    · rw [fuNestWeight_of_lt ha (by omega) (by omega)]
  have h3 : ((k : ℝ) - a - c - 1) * fuNestWeight (k - 1) a c =
      ((k : ℝ) - a - c - 1) * (-fuPhi (k - 1) a) := by
    rcases Nat.eq_or_lt_of_le (by omega : a + c + 1 ≤ k) with rfl | hlt
    · have hz : ((a + c + 1 : ℕ) : ℝ) - a - c - 1 = 0 := by
        push_cast
        ring
      rw [hz, zero_mul, zero_mul]
    · rw [fuNestWeight_of_lt ha hc (by omega)]
  rw [h2, h3, fuNestWeight_of_lt ha hc hac]
  rcases Nat.eq_or_lt_of_le ha with rfl | ha2
  · rw [fuNestWeight_of_not (m := k - 1) (a := 1 - 1) (by omega), ite_eq_left rfl]
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · obtain rfl : k = 3 := by omega
      rw [show (3 : ℕ) - 1 = 2 from rfl, fuPhi_three_one]
      push_cast
      ring
    · obtain ⟨e, rfl⟩ : ∃ e, k = e + 4 := ⟨k - 4, by omega⟩
      rw [show e + 4 - 1 = e + 3 from rfl]
      have h := fuPhi_step_one e
      push_cast
      linear_combination (-1 : ℝ) * h
  · obtain ⟨s, rfl⟩ : ∃ s, a = s + 2 := ⟨a - 2, by omega⟩
    rw [ite_eq_right (by omega), sub_zero, show s + 2 - 1 = s + 1 from rfl,
      fuNestWeight_of_lt (m := k - 1) (a := s + 1) (c := c) (by omega) hc (by omega)]
    rcases Nat.eq_or_lt_of_le (by omega : s + 4 ≤ k) with rfl | hk5
    · rw [show s + 4 - 1 = s + 3 from rfl]
      have h := fuPhi_step_top s
      push_cast
      linear_combination (-1 : ℝ) * h
    · obtain ⟨E, rfl⟩ : ∃ E, k = s + E + 5 := ⟨k - s - 5, by omega⟩
      rw [show s + E + 5 - 1 = s + E + 4 from rfl]
      have h := fuPhi_step s E
      push_cast
      linear_combination (-1 : ℝ) * h

noncomputable def sfsCladeNestCoeff (m a c : ℕ) : ℝ :=
  fuNestWeight m a c / ((m.choose a : ℝ) * ((m - a).choose c : ℝ))

theorem sfsCladeNestCoeff_of_le_one {k : ℕ} (hk : k ≤ 1) (a c : ℕ) :
    sfsCladeNestCoeff k a c = 0 := by
  unfold sfsCladeNestCoeff
  rw [fuNestWeight_of_not (by omega), zero_div]

theorem choose_mul_sfsCladeNestCoeff (n a c : ℕ) :
    (n.choose a : ℝ) * ((n - a).choose c : ℝ) * sfsCladeNestCoeff n a c =
      fuNestWeight n a c := by
  unfold sfsCladeNestCoeff
  by_cases h : 1 ≤ a ∧ 1 ≤ c ∧ a + c < n
  · have hc : (n.choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hd : ((n - a).choose c : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    field_simp
  · rw [fuNestWeight_of_not h, zero_div, mul_zero]

theorem sfsCladeNestCoeff_step {k a c : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hac : a + c ≤ k) :
    (a.choose 2 : ℝ) * sfsCladeNestCoeff (k - 1) (a - 1) c +
        (c.choose 2 : ℝ) * sfsCladeNestCoeff (k - 1) a (c - 1) +
        ((k - a - c).choose 2 : ℝ) * sfsCladeNestCoeff (k - 1) a c =
      (k.choose 2 : ℝ) * sfsCladeNestCoeff k a c -
        (if a = 1 then Coalescent.sfsCladeCoeff k (a + c) else 0) := by
  rcases Nat.eq_or_lt_of_le hac with he | hlt
  · have hz : (if a = 1 then Coalescent.sfsCladeCoeff k (a + c) else 0) = 0 := by
      split_ifs
      · unfold Coalescent.sfsCladeCoeff
        rw [ite_eq_right (by omega)]
      · rfl
    unfold sfsCladeNestCoeff
    rw [hz, fuNestWeight_of_not (m := k - 1) (a := a - 1) (c := c) (by omega),
      fuNestWeight_of_not (m := k - 1) (a := a) (c := c - 1) (by omega),
      fuNestWeight_of_not (m := k - 1) (a := a) (c := c) (by omega),
      fuNestWeight_of_not (m := k) (a := a) (c := c) (by omega)]
    ring
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hCa : (k.choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hCc : ((k - a).choose c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hka : (k : ℝ) - (a : ℝ) ≠ 0 := by
    have : (a : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : a < k)
    linarith
  have hsub : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) := Nat.cast_sub (by omega)
  have hC1 : ((k - 1).choose (a - 1) : ℝ) = (k.choose a : ℝ) * (a : ℝ) / (k : ℝ) := by
    rw [eq_div_iff hk0, choose_pred_pred_cast ha (by omega)]
  have hC2 : ((k - 1).choose a : ℝ) =
      (k.choose a : ℝ) * ((k : ℝ) - (a : ℝ)) / (k : ℝ) := by
    rw [eq_div_iff hk0, choose_pred_cast (by omega) (by omega)]
  have hC3 : ((k - a - 1).choose (c - 1) : ℝ) =
      ((k - a).choose c : ℝ) * (c : ℝ) / ((k : ℝ) - (a : ℝ)) := by
    rw [eq_div_iff hka, ← hsub, choose_pred_pred_cast hc (by omega)]
  have hC4 : ((k - a - 1).choose c : ℝ) =
      ((k - a).choose c : ℝ) * ((k : ℝ) - (a : ℝ) - (c : ℝ)) / ((k : ℝ) - (a : ℝ)) := by
    rw [eq_div_iff hka, ← hsub, choose_pred_cast (by omega) (by omega)]
  have hkac : (k : ℝ) - (a : ℝ) - (c : ℝ) ≠ 0 := by
    have : (a : ℝ) + (c : ℝ) < (k : ℝ) := by exact_mod_cast hlt
    linarith
  have hcast : ((k - a - c : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) - (c : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hW := fuNestWeight_step ha hc hlt
  have t1 : (a.choose 2 : ℝ) * sfsCladeNestCoeff (k - 1) (a - 1) c =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose c : ℝ))) *
        (((a : ℝ) - 1) * fuNestWeight (k - 1) (a - 1) c) := by
    unfold sfsCladeNestCoeff
    rw [show k - 1 - (a - 1) = k - a by omega, hC1, Nat.cast_choose_two]
    field_simp
  have t2 : (c.choose 2 : ℝ) * sfsCladeNestCoeff (k - 1) a (c - 1) =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose c : ℝ))) *
        (((c : ℝ) - 1) * fuNestWeight (k - 1) a (c - 1)) := by
    unfold sfsCladeNestCoeff
    rw [show k - 1 - a = k - a - 1 by omega, hC2, hC3, Nat.cast_choose_two]
    field_simp
  have t3 : ((k - a - c).choose 2 : ℝ) * sfsCladeNestCoeff (k - 1) a c =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose c : ℝ))) *
        (((k : ℝ) - a - c - 1) * fuNestWeight (k - 1) a c) := by
    unfold sfsCladeNestCoeff
    rw [show k - 1 - a = k - a - 1 by omega, hC2, hC4, Nat.cast_choose_two, hcast]
    field_simp
  have t4 : (k.choose 2 : ℝ) * sfsCladeNestCoeff k a c =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose c : ℝ))) *
        (((k : ℝ) - 1) * fuNestWeight k a c) := by
    unfold sfsCladeNestCoeff
    rw [Nat.cast_choose_two]
    field_simp
  have t5 : (if a = 1 then Coalescent.sfsCladeCoeff k (a + c) else 0) =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose c : ℝ))) *
        (if a = 1 then 4 / (k : ℝ) else 0) := by
    split_ifs with h
    · subst h
      have hCk : (k.choose (1 + c) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have hE : ((k - 1).choose c : ℝ) * (k : ℝ) =
          (k.choose (1 + c) : ℝ) * ((1 + c : ℕ) : ℝ) := by
        have h := choose_pred_pred_cast (k := k) (a := 1 + c) (by omega) (by omega)
        rwa [show 1 + c - 1 = c by omega] at h
      have hE' : ((k - 1).choose c : ℝ) =
          (k.choose (1 + c) : ℝ) * ((1 + c : ℕ) : ℝ) / (k : ℝ) := by
        rw [eq_div_iff hk0, hE]
      have h1c : ((1 + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 1 + c ≠ 0)
      unfold Coalescent.sfsCladeCoeff
      rw [ite_eq_left (by omega), Nat.choose_one_right, hE']
      field_simp
      norm_num
    · ring
  linear_combination t1 + t2 + t3 - t4 + t5 +
    (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose c : ℝ))) * hW

/-- Source: fu1995, eq. (2)–(3), pp. 174–175. -/
noncomputable def fuSigma (n i j : ℕ) : ℝ :=
  if i = j then fuSigmaDiag n i
  else if i + j < n then (fuBeta n (max i j + 1) - fuBeta n (max i j)) / 2
  else if i + j = n then
    ((harmonic (n - 1) : ℝ) - (harmonic (i - 1) : ℝ)) / ((n : ℝ) - i) +
      ((harmonic (n - 1) : ℝ) - (harmonic (j - 1) : ℝ)) / ((n : ℝ) - j) -
      (fuBeta n (max i j) + fuBeta n (min i j + 1)) / 2 - 1 / ((i : ℝ) * (j : ℝ))
  else (fuBeta n (min i j) - fuBeta n (min i j + 1)) / 2 - 1 / ((i : ℝ) * (j : ℝ))

theorem fuSigma_self (n i : ℕ) : fuSigma n i i = fuSigmaDiag n i := ite_eq_left rfl

theorem fuSigma_comm (n i j : ℕ) : fuSigma n i j = fuSigma n j i := by
  by_cases h : i = j
  · rw [h]
  · unfold fuSigma
    rw [ite_eq_right h, ite_eq_right (Ne.symm h), max_comm j i, min_comm j i, add_comm j i,
      mul_comm (j : ℝ) (i : ℝ)]
    split_ifs <;> ring

theorem fuSigma_eq {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j < n) :
    fuPairWeight n i j + fuNestWeight n i (j - i) =
      4 * fuSigma n i j + 4 / ((i : ℝ) * (j : ℝ)) := by
  unfold fuSigma
  rw [ite_eq_right (by omega), max_eq_right hij.le, min_eq_left hij.le,
    fuNestWeight_of_lt hi (by omega) (by omega)]
  split_ifs with h1 h2
  · rw [fuPairWeight_of_lt hi (by omega) h1]
    unfold fuPhi
    ring
  · rw [fuPairWeight_of_eq hi (by omega) h2]
    unfold fuPsi fuPhi
    ring
  · rw [fuPairWeight_of_not (by omega)]
    unfold fuPhi
    ring

end Rhone.Statistics
