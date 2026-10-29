/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SfsMarkedSpectrumCoeff
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Coefficients of the variance of the site frequency spectrum

Source: fu1995, eq. (2), (4)–(5), pp. 174–175. -/

@[expose] public section
namespace Rhone.Statistics

/-- Source: fu1995, eq. (5), p. 175. -/
noncomputable def fuBeta (n i : ℕ) : ℝ :=
  2 * (n : ℝ) * ((harmonic n : ℝ) - (harmonic (i - 1) : ℝ)) /
      (((n : ℝ) - i + 1) * ((n : ℝ) - i)) - 2 / ((n : ℝ) - i)

noncomputable def fuPhi (m a : ℕ) : ℝ := 2 * (fuBeta m (a + 1) - fuBeta m a)

noncomputable def fuPsi (m a : ℕ) : ℝ :=
  4 * ((harmonic (m - 1) : ℝ) - (harmonic (a - 1) : ℝ)) / ((m : ℝ) - a) - 2 * fuBeta m a

theorem harmonic_cast_of_eq_succ {m n : ℕ} (h : m = n + 1) :
    (harmonic m : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
  subst h
  rw [harmonic_succ]
  push_cast
  ring

theorem fuBeta_of_eq {n i : ℕ} (j D : ℕ) (hi : i = j + 1) (hn : n = j + 1 + D) :
    fuBeta n i = 2 * (n : ℝ) * ((harmonic n : ℝ) - (harmonic j : ℝ)) /
      (((D : ℝ) + 1) * (D : ℝ)) - 2 / (D : ℝ) := by
  subst hi hn
  unfold fuBeta
  rw [Nat.add_sub_cancel]
  push_cast
  ring

theorem fuPhi_of_eq {m a : ℕ} (j E : ℕ) (ha : a = j + 1) (hm : m = j + 2 + E) :
    fuPhi m a = 2 * ((2 * (m : ℝ) * ((harmonic m : ℝ) - (harmonic (j + 1) : ℝ)) /
        (((E : ℝ) + 1) * (E : ℝ)) - 2 / (E : ℝ)) -
      (2 * (m : ℝ) * ((harmonic m : ℝ) - (harmonic j : ℝ)) /
        (((E : ℝ) + 2) * ((E : ℝ) + 1)) - 2 / ((E : ℝ) + 1))) := by
  subst ha
  unfold fuPhi
  rw [fuBeta_of_eq (j + 1) E rfl (by omega), fuBeta_of_eq j (E + 1) rfl (by omega)]
  push_cast
  ring

theorem fuPsi_of_eq {m a : ℕ} (j D p : ℕ) (ha : a = j + 1) (hm : m = j + 1 + D)
    (hp : m = p + 1) :
    fuPsi m a = 4 * ((harmonic p : ℝ) - (harmonic j : ℝ)) / (D : ℝ) -
      2 * (2 * (m : ℝ) * ((harmonic m : ℝ) - (harmonic j : ℝ)) /
        (((D : ℝ) + 1) * (D : ℝ)) - 2 / (D : ℝ)) := by
  subst ha
  unfold fuPsi
  rw [fuBeta_of_eq j D rfl hm, Nat.add_sub_cancel, show m - 1 = p by omega]
  have hc : (m : ℝ) - ((j + 1 : ℕ) : ℝ) = (D : ℝ) := by
    rw [hm]
    push_cast
    ring
  rw [hc]

theorem fuBeta_step_one (i : ℕ) :
    ((i : ℝ) + 1) * fuBeta (i + 2) 1 =
        ((i : ℝ) + 2) * fuBeta (i + 3) 1 - 2 / ((i : ℝ) + 3) := by
  rw [fuBeta_of_eq (n := i + 2) (i := 1) 0 (i + 1) rfl (by omega),
    fuBeta_of_eq (n := i + 3) (i := 1) 0 (i + 2) rfl (by omega),
    harmonic_cast_of_eq_succ (m := i + 3) (n := i + 2) rfl, harmonic_zero]
  push_cast
  field_simp
  ring

theorem fuBeta_step_top (s : ℕ) :
    ((s : ℝ) + 1) * fuBeta (s + 2) (s + 1) = ((s : ℝ) + 2) * fuBeta (s + 3) (s + 2) := by
  rw [fuBeta_of_eq (n := s + 2) (i := s + 1) s 1 rfl (by omega),
    fuBeta_of_eq (n := s + 3) (i := s + 2) (s + 1) 1 rfl (by omega),
    harmonic_cast_of_eq_succ (m := s + 3) (n := s + 2) rfl,
    harmonic_cast_of_eq_succ (m := s + 2) (n := s + 1) rfl,
    harmonic_cast_of_eq_succ (m := s + 1) (n := s) rfl]
  push_cast
  field_simp
  ring

theorem fuBeta_step_mid (s e : ℕ) :
    ((s : ℝ) + 1) * fuBeta (s + e + 3) (s + 1) + ((e : ℝ) + 1) * fuBeta (s + e + 3) (s + 2) =
      ((s : ℝ) + e + 3) * fuBeta (s + e + 4) (s + 2) := by
  rw [fuBeta_of_eq (n := s + e + 3) (i := s + 1) s (e + 2) rfl (by omega),
    fuBeta_of_eq (n := s + e + 3) (i := s + 2) (s + 1) (e + 1) rfl (by omega),
    fuBeta_of_eq (n := s + e + 4) (i := s + 2) (s + 1) (e + 2) rfl (by omega),
    harmonic_cast_of_eq_succ (m := s + e + 4) (n := s + e + 3) rfl,
    harmonic_cast_of_eq_succ (m := s + 1) (n := s) rfl]
  push_cast
  field_simp
  ring

theorem fuPhi_step (s E : ℕ) :
    ((s : ℝ) + 1) * fuPhi (s + E + 4) (s + 1) + ((E : ℝ) + 1) * fuPhi (s + E + 4) (s + 2) =
      ((s : ℝ) + E + 4) * fuPhi (s + E + 5) (s + 2) := by
  rw [fuPhi_of_eq (m := s + E + 4) (a := s + 1) s (E + 2) rfl (by omega),
    fuPhi_of_eq (m := s + E + 4) (a := s + 2) (s + 1) (E + 1) rfl (by omega),
    fuPhi_of_eq (m := s + E + 5) (a := s + 2) (s + 1) (E + 2) rfl (by omega),
    harmonic_cast_of_eq_succ (m := s + E + 5) (n := s + E + 4) rfl,
    harmonic_cast_of_eq_succ (m := s + 1 + 1) (n := s + 1) rfl,
    harmonic_cast_of_eq_succ (m := s + 1) (n := s) rfl]
  push_cast
  field_simp
  ring

theorem fuPhi_step_one (e : ℕ) :
    ((e : ℝ) + 1) * fuPhi (e + 3) 1 =
      ((e : ℝ) + 3) * fuPhi (e + 4) 1 + 4 / ((e : ℝ) + 4) := by
  rw [fuPhi_of_eq (m := e + 3) (a := 1) 0 (e + 1) rfl (by omega),
    fuPhi_of_eq (m := e + 4) (a := 1) 0 (e + 2) rfl (by omega),
    harmonic_cast_of_eq_succ (m := e + 4) (n := e + 3) rfl,
    harmonic_cast_of_eq_succ (m := 0 + 1) (n := 0) rfl, harmonic_zero]
  push_cast
  field_simp
  ring

theorem fuPhi_step_top (s : ℕ) :
    ((s : ℝ) + 1) * fuPhi (s + 3) (s + 1) = ((s : ℝ) + 3) * fuPhi (s + 4) (s + 2) := by
  rw [fuPhi_of_eq (m := s + 3) (a := s + 1) s 1 rfl (by omega),
    fuPhi_of_eq (m := s + 4) (a := s + 2) (s + 1) 1 rfl (by omega),
    harmonic_cast_of_eq_succ (m := s + 4) (n := s + 3) rfl,
    harmonic_cast_of_eq_succ (m := s + 3) (n := s + 2) rfl,
    harmonic_cast_of_eq_succ (m := s + 2) (n := s + 1) rfl,
    harmonic_cast_of_eq_succ (m := s + 1) (n := s) rfl]
  push_cast
  field_simp
  ring

theorem fuPsi_step (s t : ℕ) :
    ((s : ℝ) + 1) * (fuPsi (s + t + 3) (s + 1) + fuPsi (s + t + 3) (t + 2)) +
        ((t : ℝ) + 1) * (fuPsi (s + t + 3) (s + 2) + fuPsi (s + t + 3) (t + 1)) =
      ((s : ℝ) + t + 3) * (fuPsi (s + t + 4) (s + 2) + fuPsi (s + t + 4) (t + 2)) := by
  rw [fuPsi_of_eq (m := s + t + 3) (a := s + 1) s (t + 2) (s + t + 2) rfl (by omega) rfl,
    fuPsi_of_eq (m := s + t + 3) (a := t + 2) (t + 1) (s + 1) (s + t + 2) rfl (by omega) rfl,
    fuPsi_of_eq (m := s + t + 3) (a := s + 2) (s + 1) (t + 1) (s + t + 2) rfl (by omega) rfl,
    fuPsi_of_eq (m := s + t + 3) (a := t + 1) t (s + 2) (s + t + 2) rfl (by omega) rfl,
    fuPsi_of_eq (m := s + t + 4) (a := s + 2) (s + 1) (t + 2) (s + t + 3) rfl (by omega) rfl,
    fuPsi_of_eq (m := s + t + 4) (a := t + 2) (t + 1) (s + 2) (s + t + 3) rfl (by omega) rfl,
    harmonic_cast_of_eq_succ (m := s + t + 4) (n := s + t + 3) rfl,
    harmonic_cast_of_eq_succ (m := s + t + 3) (n := s + t + 2) rfl,
    harmonic_cast_of_eq_succ (m := s + 1) (n := s) rfl,
    harmonic_cast_of_eq_succ (m := t + 1) (n := t) rfl]
  push_cast
  field_simp
  ring

theorem fuPsi_step_one (t : ℕ) :
    ((t : ℝ) + 1) * (fuPsi (t + 2) 1 + fuPsi (t + 2) (t + 1)) =
      ((t : ℝ) + 2) * (fuPsi (t + 3) 1 + fuPsi (t + 3) (t + 2)) -
        4 / (((t : ℝ) + 2) * ((t : ℝ) + 3)) := by
  rw [fuPsi_of_eq (m := t + 2) (a := 1) 0 (t + 1) (t + 1) rfl (by omega) rfl,
    fuPsi_of_eq (m := t + 2) (a := t + 1) t 1 (t + 1) rfl (by omega) rfl,
    fuPsi_of_eq (m := t + 3) (a := 1) 0 (t + 2) (t + 2) rfl (by omega) rfl,
    fuPsi_of_eq (m := t + 3) (a := t + 2) (t + 1) 1 (t + 2) rfl (by omega) rfl,
    harmonic_cast_of_eq_succ (m := t + 3) (n := t + 2) rfl,
    harmonic_cast_of_eq_succ (m := t + 2) (n := t + 1) rfl,
    harmonic_cast_of_eq_succ (m := t + 1) (n := t) rfl, harmonic_zero]
  push_cast
  field_simp
  ring

theorem fuPsi_two_one : fuPsi 2 1 = 2 := by
  norm_num [fuPsi, fuBeta, harmonic, Finset.sum_range_succ]

theorem fuPhi_three_one : fuPhi 3 1 = -2 / 3 := by
  norm_num [fuPhi, fuBeta, harmonic, Finset.sum_range_succ]

theorem fuBeta_two_one : fuBeta 2 1 = 1 := by
  norm_num [fuBeta, harmonic, Finset.sum_range_succ]

noncomputable def fuSqWeight (m a : ℕ) : ℝ := if 1 ≤ a ∧ a < m then fuBeta m a else 0

theorem fuSqWeight_of_lt {m a : ℕ} (ha : 1 ≤ a) (ham : a < m) :
    fuSqWeight m a = fuBeta m a := ite_eq_left ⟨ha, ham⟩

theorem fuSqWeight_of_not {m a : ℕ} (h : ¬ (1 ≤ a ∧ a < m)) : fuSqWeight m a = 0 :=
    ite_eq_right h

theorem fuSqWeight_step {k a : ℕ} (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ((a : ℝ) - 1) * fuSqWeight (k - 1) (a - 1) + ((k : ℝ) - a - 1) * fuSqWeight (k - 1) a =
      ((k : ℝ) - 1) * fuSqWeight k a - if a = 1 then 2 / (k : ℝ) else 0 := by
  rcases Nat.eq_or_lt_of_le hak with rfl | hlt
  · rw [fuSqWeight_of_not (m := a - 1) (a := a - 1) (by omega),
      fuSqWeight_of_not (m := a - 1) (a := a) (by omega),
      fuSqWeight_of_not (m := a) (a := a) (by omega), ite_eq_right (by omega)]
    ring
  rcases Nat.eq_or_lt_of_le ha with rfl | ha2
  · rw [fuSqWeight_of_not (m := k - 1) (a := 1 - 1) (by omega),
      fuSqWeight_of_lt (m := k) (a := 1) le_rfl hlt, ite_eq_left rfl]
    rcases Nat.lt_or_ge k 3 with h3 | h3
    · obtain rfl : k = 2 := by omega
      rw [fuSqWeight_of_not (m := 2 - 1) (a := 1) (by omega), fuBeta_two_one]
      norm_num
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 3 := ⟨k - 3, by omega⟩
      rw [show i + 3 - 1 = i + 2 from rfl,
        fuSqWeight_of_lt (m := i + 2) (a := 1) le_rfl (by omega)]
      have h := fuBeta_step_one i
      push_cast
      linear_combination h
  · obtain ⟨s, rfl⟩ : ∃ s, a = s + 2 := ⟨a - 2, by omega⟩
    rw [ite_eq_right (by omega), sub_zero, show s + 2 - 1 = s + 1 from rfl]
    rcases Nat.eq_or_lt_of_le (by omega : s + 3 ≤ k) with rfl | hk3
    · rw [show s + 3 - 1 = s + 2 from rfl,
        fuSqWeight_of_lt (m := s + 2) (a := s + 1) (by omega) (by omega),
        fuSqWeight_of_not (m := s + 2) (a := s + 2) (by omega),
        fuSqWeight_of_lt (m := s + 3) (a := s + 2) (by omega) (by omega)]
      have h := fuBeta_step_top s
      push_cast
      linear_combination h
    · obtain ⟨e, rfl⟩ : ∃ e, k = s + e + 4 := ⟨k - s - 4, by omega⟩
      rw [show s + e + 4 - 1 = s + e + 3 from rfl,
        fuSqWeight_of_lt (m := s + e + 3) (a := s + 1) (by omega) (by omega),
        fuSqWeight_of_lt (m := s + e + 3) (a := s + 2) (by omega) (by omega),
        fuSqWeight_of_lt (m := s + e + 4) (a := s + 2) (by omega) (by omega)]
      have h := fuBeta_step_mid s e
      push_cast
      linear_combination h

noncomputable def fuPairWeight (m a b : ℕ) : ℝ :=
  if 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ m then
    if a + b < m then fuPhi m a + fuPhi m b + 4 / ((a : ℝ) * (b : ℝ))
    else fuPsi m a + fuPsi m b
  else 0

theorem fuPairWeight_of_lt {m a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b < m) :
    fuPairWeight m a b = fuPhi m a + fuPhi m b + 4 / ((a : ℝ) * (b : ℝ)) := by
  unfold fuPairWeight
  rw [ite_eq_left ⟨ha, hb, h.le⟩, ite_eq_left h]

theorem fuPairWeight_of_eq {m a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b = m) :
    fuPairWeight m a b = fuPsi m a + fuPsi m b := by
  unfold fuPairWeight
  rw [ite_eq_left ⟨ha, hb, h.le⟩, ite_eq_right (by omega)]

theorem fuPairWeight_of_not {m a b : ℕ} (h : ¬ (1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ m)) :
    fuPairWeight m a b = 0 := ite_eq_right h

theorem fuPairWeight_comm (m a b : ℕ) : fuPairWeight m a b = fuPairWeight m b a := by
  by_cases h : 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ m
  · rcases Nat.eq_or_lt_of_le h.2.2 with he | hl
    · rw [fuPairWeight_of_eq h.1 h.2.1 he, fuPairWeight_of_eq h.2.1 h.1 (by omega)]
      ring
    · rw [fuPairWeight_of_lt h.1 h.2.1 hl, fuPairWeight_of_lt h.2.1 h.1 (by omega)]
      ring
  · rw [fuPairWeight_of_not h, fuPairWeight_of_not (by omega)]

private theorem fuPairWeight_step_aux {k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a + b ≤ k)
    (hord : 2 ≤ a → 2 ≤ b) :
    ((a : ℝ) - 1) * fuPairWeight (k - 1) (a - 1) b +
        ((b : ℝ) - 1) * fuPairWeight (k - 1) a (b - 1) +
        ((k : ℝ) - a - b - 1) * fuPairWeight (k - 1) a b =
      ((k : ℝ) - 1) * fuPairWeight k a b -
        (if a = 1 then 4 * ((k : ℝ) - b) / ((b : ℝ) * (k : ℝ)) else 0) -
        (if b = 1 then 4 * ((k : ℝ) - a) / ((a : ℝ) * (k : ℝ)) else 0) := by
  rcases Nat.eq_or_lt_of_le ha with rfl | ha2
  · rcases Nat.eq_or_lt_of_le hb with rfl | hb2
    · rw [ite_eq_left rfl]
      rcases Nat.lt_or_ge k 4 with h4 | h4
      · rcases Nat.eq_or_lt_of_le hab with rfl | h3
        · rw [fuPairWeight_of_not (m := 1 + 1 - 1) (a := 1) (b := 1) (by omega),
            fuPairWeight_of_eq (m := 1 + 1) (a := 1) (b := 1) le_rfl le_rfl rfl, fuPsi_two_one]
          norm_num
        · obtain rfl : k = 3 := by omega
          rw [fuPairWeight_of_lt (m := 3) (a := 1) (b := 1) le_rfl le_rfl (by omega),
            fuPhi_three_one]
          norm_num
      · obtain ⟨e, rfl⟩ : ∃ e, k = e + 4 := ⟨k - 4, by omega⟩
        rw [show e + 4 - 1 = e + 3 from rfl,
          fuPairWeight_of_lt (m := e + 3) (a := 1) (b := 1) le_rfl le_rfl (by omega),
          fuPairWeight_of_lt (m := e + 4) (a := 1) (b := 1) le_rfl le_rfl (by omega)]
        have h := fuPhi_step_one e
        have hc : 4 * ((e : ℝ) + 1) + 8 / ((e : ℝ) + 4) -
            (4 * ((e : ℝ) + 3) - 8 * ((e : ℝ) + 3) / ((e : ℝ) + 4)) = 0 := by
          field_simp
          ring
        push_cast
        linear_combination 2 * h + hc
    · obtain ⟨t, rfl⟩ : ∃ t, b = t + 2 := ⟨b - 2, by omega⟩
      rw [ite_eq_left rfl, ite_eq_right (by omega), sub_zero, show t + 2 - 1 = t + 1 from rfl]
      rcases Nat.lt_or_ge k (t + 5) with h5 | h5
      · rcases Nat.eq_or_lt_of_le hab with rfl | h3
        · rw [show 1 + (t + 2) - 1 = t + 2 by omega, show 1 + (t + 2) = t + 3 by omega,
            fuPairWeight_of_eq (m := t + 2) (a := 1) (b := t + 1) le_rfl (by omega) (by omega),
            fuPairWeight_of_not (m := t + 2) (a := 1) (b := t + 2) (by omega),
            fuPairWeight_of_eq (m := t + 3) (a := 1) (b := t + 2) le_rfl (by omega) (by omega)]
          have h := fuPsi_step_one t
          push_cast
          linear_combination h
        · obtain rfl : k = t + 4 := by omega
          rw [show t + 4 - 1 = t + 3 from rfl,
            fuPairWeight_of_lt (m := t + 3) (a := 1) (b := t + 1) le_rfl (by omega) (by omega),
            fuPairWeight_of_lt (m := t + 4) (a := 1) (b := t + 2) le_rfl (by omega) (by omega)]
          have h1 := fuPhi_step_one t
          have h2 := fuPhi_step_top t
          have hc : ((t : ℝ) + 1) * (4 / ((t : ℝ) + 1)) -
              ((t : ℝ) + 3) * (4 / ((t : ℝ) + 2)) +
              8 / (((t : ℝ) + 2) * ((t : ℝ) + 4)) + 4 / ((t : ℝ) + 4) = 0 := by
            field_simp
            ring
          push_cast
          linear_combination h1 + h2 + hc
      · obtain ⟨e, rfl⟩ : ∃ e, k = t + e + 5 := ⟨k - t - 5, by omega⟩
        rw [show t + e + 5 - 1 = t + e + 4 from rfl,
          fuPairWeight_of_lt (m := t + e + 4) (a := 1) (b := t + 1) le_rfl (by omega) (by omega),
          fuPairWeight_of_lt (m := t + e + 4) (a := 1) (b := t + 2) le_rfl (by omega) (by omega),
          fuPairWeight_of_lt (m := t + e + 5) (a := 1) (b := t + 2) le_rfl (by omega) (by omega)]
        have h1 := fuPhi_step_one (t + e + 1)
        rw [show t + e + 1 + 3 = t + e + 4 from rfl, show t + e + 1 + 4 = t + e + 5 from rfl] at h1
        have h2 := fuPhi_step t e
        have hc : ((t : ℝ) + 1) * (4 / ((t : ℝ) + 1)) +
            ((e : ℝ) + 1) * (4 / ((t : ℝ) + 2)) -
            ((t : ℝ) + e + 4) * (4 / ((t : ℝ) + 2)) +
            4 * ((e : ℝ) + 3) / (((t : ℝ) + 2) * ((t : ℝ) + e + 5)) +
            4 / ((t : ℝ) + e + 5) = 0 := by
          field_simp
          ring
        push_cast at h1 ⊢
        linear_combination h1 + h2 + hc
  · have hb2 := hord ha2
    obtain ⟨s, rfl⟩ : ∃ s, a = s + 2 := ⟨a - 2, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, b = t + 2 := ⟨b - 2, by omega⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero, sub_zero,
      show s + 2 - 1 = s + 1 from rfl, show t + 2 - 1 = t + 1 from rfl]
    have hc : ((s : ℝ) + 1) * (4 / (((s : ℝ) + 1) * ((t : ℝ) + 2))) +
        ((t : ℝ) + 1) * (4 / (((s : ℝ) + 2) * ((t : ℝ) + 1))) -
        ((s : ℝ) + t + 4) * (4 / (((s : ℝ) + 2) * ((t : ℝ) + 2))) = 0 := by
      field_simp
      ring
    rcases Nat.lt_or_ge k (s + t + 6) with h6 | h6
    · rcases Nat.eq_or_lt_of_le hab with rfl | h3
      · rw [show s + 2 + (t + 2) - 1 = s + t + 3 by omega,
          show s + 2 + (t + 2) = s + t + 4 by omega,
          fuPairWeight_of_eq (m := s + t + 3) (a := s + 1) (b := t + 2) (by omega) (by omega)
            (by omega),
          fuPairWeight_of_eq (m := s + t + 3) (a := s + 2) (b := t + 1) (by omega) (by omega)
            (by omega),
          fuPairWeight_of_not (m := s + t + 3) (a := s + 2) (b := t + 2) (by omega),
          fuPairWeight_of_eq (m := s + t + 4) (a := s + 2) (b := t + 2) (by omega) (by omega)
            (by omega)]
        have h := fuPsi_step s t
        push_cast
        linear_combination h
      · obtain rfl : k = s + t + 5 := by omega
        rw [show s + t + 5 - 1 = s + t + 4 from rfl,
          fuPairWeight_of_lt (m := s + t + 4) (a := s + 1) (b := t + 2) (by omega) (by omega)
            (by omega),
          fuPairWeight_of_lt (m := s + t + 4) (a := s + 2) (b := t + 1) (by omega) (by omega)
            (by omega),
          fuPairWeight_of_lt (m := s + t + 5) (a := s + 2) (b := t + 2) (by omega) (by omega)
            (by omega)]
        have h1 := fuPhi_step s t
        have h2 := fuPhi_step t s
        rw [show t + s + 4 = s + t + 4 by omega, show t + s + 5 = s + t + 5 by omega] at h2
        push_cast
        linear_combination h1 + h2 + hc
    · obtain ⟨e, rfl⟩ : ∃ e, k = s + t + e + 6 := ⟨k - s - t - 6, by omega⟩
      rw [show s + t + e + 6 - 1 = s + t + e + 5 from rfl,
        fuPairWeight_of_lt (m := s + t + e + 5) (a := s + 1) (b := t + 2) (by omega) (by omega)
          (by omega),
        fuPairWeight_of_lt (m := s + t + e + 5) (a := s + 2) (b := t + 1) (by omega) (by omega)
          (by omega),
        fuPairWeight_of_lt (m := s + t + e + 5) (a := s + 2) (b := t + 2) (by omega) (by omega)
          (by omega),
        fuPairWeight_of_lt (m := s + t + e + 6) (a := s + 2) (b := t + 2) (by omega) (by omega)
          (by omega)]
      have h1 := fuPhi_step s (t + e + 1)
      rw [show s + (t + e + 1) + 4 = s + t + e + 5 by omega,
        show s + (t + e + 1) + 5 = s + t + e + 6 by omega] at h1
      have h2 := fuPhi_step t (s + e + 1)
      rw [show t + (s + e + 1) + 4 = s + t + e + 5 by omega,
        show t + (s + e + 1) + 5 = s + t + e + 6 by omega] at h2
      have hc2 : ((s : ℝ) + 1) * (4 / (((s : ℝ) + 1) * ((t : ℝ) + 2))) +
          ((t : ℝ) + 1) * (4 / (((s : ℝ) + 2) * ((t : ℝ) + 1))) +
          ((e : ℝ) + 1) * (4 / (((s : ℝ) + 2) * ((t : ℝ) + 2))) -
          ((s : ℝ) + t + e + 5) * (4 / (((s : ℝ) + 2) * ((t : ℝ) + 2))) = 0 := by
        field_simp
        ring
      push_cast at h1 h2 ⊢
      linear_combination h1 + h2 + hc2

theorem fuPairWeight_step {k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ k) :
    ((a : ℝ) - 1) * fuPairWeight (k - 1) (a - 1) b +
        ((b : ℝ) - 1) * fuPairWeight (k - 1) a (b - 1) +
        ((k : ℝ) - a - b - 1) * fuPairWeight (k - 1) a b =
      ((k : ℝ) - 1) * fuPairWeight k a b -
        (if a = 1 then 4 * ((k : ℝ) - b) / ((b : ℝ) * (k : ℝ)) else 0) -
        (if b = 1 then 4 * ((k : ℝ) - a) / ((a : ℝ) * (k : ℝ)) else 0) := by
  by_cases hord : 2 ≤ a → 2 ≤ b
  · exact fuPairWeight_step_aux ha hb hab hord
  · have h := fuPairWeight_step_aux hb ha (by omega : b + a ≤ k) (by omega)
    rw [fuPairWeight_comm (k - 1) (b - 1) a, fuPairWeight_comm (k - 1) b (a - 1),
      fuPairWeight_comm (k - 1) b a, fuPairWeight_comm k b a] at h
    linear_combination h

/-- Source: fu1995, eq. (2), p. 174. -/
noncomputable def fuSigmaDiag (n i : ℕ) : ℝ :=
  if 2 * i < n then fuBeta n (i + 1)
  else if 2 * i = n then
    2 * ((harmonic (n - 1) : ℝ) - (harmonic (i - 1) : ℝ)) / ((n : ℝ) - i) - 1 / (i : ℝ) ^ 2
  else fuBeta n i - 1 / (i : ℝ) ^ 2

theorem fuSigmaDiag_eq {n i : ℕ} (hi : 1 ≤ i) :
    4 * fuBeta n i + fuPairWeight n i i - 4 / (i : ℝ) ^ 2 = 4 * fuSigmaDiag n i := by
  unfold fuSigmaDiag
  split_ifs with h1 h2
  · rw [fuPairWeight_of_lt hi hi (by omega)]
    unfold fuPhi
    ring
  · rw [fuPairWeight_of_eq hi hi (by omega)]
    unfold fuPsi
    ring
  · rw [fuPairWeight_of_not (by omega)]
    ring

theorem choose_pred_pred_cast {k a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    ((k - 1).choose (a - 1) : ℝ) * (k : ℝ) = (k.choose a : ℝ) * (a : ℝ) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := Nat.add_one_mul_choose_eq k a
  have hR : (((k + 1) * k.choose a : ℕ) : ℝ) =
      (((k + 1).choose (a + 1) * (a + 1) : ℕ) : ℝ) := by
    rw [h]
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  push_cast at hR ⊢
  linarith

theorem choose_pred_cast {k a : ℕ} (hk : 1 ≤ k) (hak : a ≤ k) :
    ((k - 1).choose a : ℝ) * (k : ℝ) = (k.choose a : ℝ) * ((k : ℝ) - (a : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := Nat.choose_mul_succ_eq k a
  have hR : ((k.choose a * (k + 1) : ℕ) : ℝ) =
      (((k + 1).choose a * (k + 1 - a) : ℕ) : ℝ) := by
    rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hak] at hR
  rw [Nat.add_sub_cancel]
  push_cast at hR ⊢
  linarith

noncomputable def sfsCladeSqCoeff (m a : ℕ) : ℝ := 4 * fuSqWeight m a / (m.choose a : ℝ)

noncomputable def sfsCladePairCoeff (m a b : ℕ) : ℝ :=
  fuPairWeight m a b / ((m.choose a : ℝ) * ((m - a).choose b : ℝ))

theorem sfsCladeSqCoeff_of_le_one {k : ℕ} (hk : k ≤ 1) (a : ℕ) : sfsCladeSqCoeff k a = 0 := by
  unfold sfsCladeSqCoeff
  rw [fuSqWeight_of_not (by omega), mul_zero, zero_div]

theorem sfsCladePairCoeff_of_le_one {k : ℕ} (hk : k ≤ 1) (a b : ℕ) :
    sfsCladePairCoeff k a b = 0 := by
  unfold sfsCladePairCoeff
  rw [fuPairWeight_of_not (by omega), zero_div]

theorem choose_mul_sfsCladeSqCoeff {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    (n.choose i : ℝ) * sfsCladeSqCoeff n i = 4 * fuBeta n i := by
  have hc : (n.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin.le).ne'
  unfold sfsCladeSqCoeff
  rw [fuSqWeight_of_lt hi hin]
  field_simp

theorem choose_mul_sfsCladePairCoeff (n a b : ℕ) :
    (n.choose a : ℝ) * ((n - a).choose b : ℝ) * sfsCladePairCoeff n a b =
      fuPairWeight n a b := by
  unfold sfsCladePairCoeff
  by_cases h : 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ n
  · have hc : (n.choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hd : ((n - a).choose b : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    field_simp
  · rw [fuPairWeight_of_not h, zero_div, mul_zero]

theorem sfsCladeSqCoeff_step {k a : ℕ} (hk : 2 ≤ k) (hak : a ≤ k) :
    (a.choose 2 : ℝ) * sfsCladeSqCoeff (k - 1) (a - 1) +
        ((k - a).choose 2 : ℝ) * sfsCladeSqCoeff (k - 1) a =
      (k.choose 2 : ℝ) * sfsCladeSqCoeff k a - if a = 1 then 2 * Coalescent.sfsCladeCoeff k 1 else
          0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · unfold sfsCladeSqCoeff
    rw [fuSqWeight_of_not (m := k - 1) (a := 0 - 1) (by omega),
      fuSqWeight_of_not (m := k) (a := 0) (by omega), ite_eq_right (by omega)]
    ring
  rcases Nat.eq_or_lt_of_le hak with rfl | hlt
  · unfold sfsCladeSqCoeff
    rw [fuSqWeight_of_not (m := a - 1) (a := a - 1) (by omega),
      fuSqWeight_of_not (m := a - 1) (a := a) (by omega),
      fuSqWeight_of_not (m := a) (a := a) (by omega), ite_eq_right (by omega)]
    ring
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hC : (k.choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hak).ne'
  have hka : (k : ℝ) - (a : ℝ) ≠ 0 := by
    have : (a : ℝ) < (k : ℝ) := by exact_mod_cast hlt
    linarith
  have hC1 : ((k - 1).choose (a - 1) : ℝ) = (k.choose a : ℝ) * (a : ℝ) / (k : ℝ) := by
    rw [eq_div_iff hk0, choose_pred_pred_cast ha hak]
  have hC2 : ((k - 1).choose a : ℝ) =
      (k.choose a : ℝ) * ((k : ℝ) - (a : ℝ)) / (k : ℝ) := by
    rw [eq_div_iff hk0, choose_pred_cast (by omega) hak]
  have hW := fuSqWeight_step hk ha hak
  have t1 : (a.choose 2 : ℝ) * sfsCladeSqCoeff (k - 1) (a - 1) =
      2 * (k : ℝ) / (k.choose a : ℝ) * (((a : ℝ) - 1) * fuSqWeight (k - 1) (a - 1)) := by
    unfold sfsCladeSqCoeff
    rw [hC1, Nat.cast_choose_two]
    field_simp
    ring
  have t2 : ((k - a).choose 2 : ℝ) * sfsCladeSqCoeff (k - 1) a =
      2 * (k : ℝ) / (k.choose a : ℝ) * (((k : ℝ) - a - 1) * fuSqWeight (k - 1) a) := by
    unfold sfsCladeSqCoeff
    rw [hC2, Nat.cast_choose_two, Nat.cast_sub hak]
    field_simp
    ring
  have t3 : (k.choose 2 : ℝ) * sfsCladeSqCoeff k a =
      2 * (k : ℝ) / (k.choose a : ℝ) * (((k : ℝ) - 1) * fuSqWeight k a) := by
    unfold sfsCladeSqCoeff
    rw [Nat.cast_choose_two]
    field_simp
    ring
  have t4 : (if a = 1 then 2 * Coalescent.sfsCladeCoeff k 1 else 0) =
      2 * (k : ℝ) / (k.choose a : ℝ) * (if a = 1 then 2 / (k : ℝ) else 0) := by
    split_ifs with h
    · subst h
      unfold Coalescent.sfsCladeCoeff
      rw [ite_eq_left hlt, Nat.choose_one_right]
      push_cast
      field_simp
    · ring
  linear_combination t1 + t2 - t3 + t4 + 2 * (k : ℝ) / (k.choose a : ℝ) * hW

theorem sfsCladePairCoeff_step {k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ k) :
    (a.choose 2 : ℝ) * sfsCladePairCoeff (k - 1) (a - 1) b +
        (b.choose 2 : ℝ) * sfsCladePairCoeff (k - 1) a (b - 1) +
        ((k - a - b).choose 2 : ℝ) * sfsCladePairCoeff (k - 1) a b =
      (k.choose 2 : ℝ) * sfsCladePairCoeff k a b -
        (if a = 1 then Coalescent.sfsCladeCoeff k b else 0) -
            (if b = 1 then Coalescent.sfsCladeCoeff k a else 0) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hCa : (k.choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hCb : ((k - a).choose b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hka : (k : ℝ) - (a : ℝ) ≠ 0 := by
    have : (a : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : a < k)
    linarith
  have hkb : (k : ℝ) - (b : ℝ) ≠ 0 := by
    have : (b : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : b < k)
    linarith
  have hsub : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) := Nat.cast_sub (by omega)
  have hC1 : ((k - 1).choose (a - 1) : ℝ) = (k.choose a : ℝ) * (a : ℝ) / (k : ℝ) := by
    rw [eq_div_iff hk0, choose_pred_pred_cast ha (by omega)]
  have hC2 : ((k - 1).choose a : ℝ) =
      (k.choose a : ℝ) * ((k : ℝ) - (a : ℝ)) / (k : ℝ) := by
    rw [eq_div_iff hk0, choose_pred_cast (by omega) (by omega)]
  have hC3 : ((k - a - 1).choose (b - 1) : ℝ) =
      ((k - a).choose b : ℝ) * (b : ℝ) / ((k : ℝ) - (a : ℝ)) := by
    rw [eq_div_iff hka, ← hsub, choose_pred_pred_cast hb (by omega)]
  have hC4 : ((k - a - 1).choose b : ℝ) =
      ((k - a).choose b : ℝ) * ((k : ℝ) - (a : ℝ) - (b : ℝ)) / ((k : ℝ) - (a : ℝ)) := by
    rw [eq_div_iff hka, ← hsub, choose_pred_cast (by omega) (by omega)]
  have hW := fuPairWeight_step ha hb hab
  have t1 : (a.choose 2 : ℝ) * sfsCladePairCoeff (k - 1) (a - 1) b =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) *
        (((a : ℝ) - 1) * fuPairWeight (k - 1) (a - 1) b) := by
    unfold sfsCladePairCoeff
    rw [show k - 1 - (a - 1) = k - a by omega, hC1, Nat.cast_choose_two]
    field_simp
  have t2 : (b.choose 2 : ℝ) * sfsCladePairCoeff (k - 1) a (b - 1) =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) *
        (((b : ℝ) - 1) * fuPairWeight (k - 1) a (b - 1)) := by
    unfold sfsCladePairCoeff
    rw [show k - 1 - a = k - a - 1 by omega, hC2, hC3, Nat.cast_choose_two]
    field_simp
  have t3 : ((k - a - b).choose 2 : ℝ) * sfsCladePairCoeff (k - 1) a b =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) *
        (((k : ℝ) - a - b - 1) * fuPairWeight (k - 1) a b) := by
    unfold sfsCladePairCoeff
    rcases Nat.eq_or_lt_of_le hab with he | hl
    · rw [fuPairWeight_of_not (m := k - 1) (a := a) (b := b) (by omega), zero_div, mul_zero,
        mul_zero, mul_zero]
    · have hkab : (k : ℝ) - (a : ℝ) - (b : ℝ) ≠ 0 := by
        have : (a : ℝ) + (b : ℝ) < (k : ℝ) := by exact_mod_cast hl
        linarith
      have hc : ((k - a - b : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) - (b : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      rw [show k - 1 - a = k - a - 1 by omega, hC2, hC4, Nat.cast_choose_two, hc]
      field_simp
  have t4 : (k.choose 2 : ℝ) * sfsCladePairCoeff k a b =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) *
        (((k : ℝ) - 1) * fuPairWeight k a b) := by
    unfold sfsCladePairCoeff
    rw [Nat.cast_choose_two]
    field_simp
  have t5 : (if a = 1 then Coalescent.sfsCladeCoeff k b else 0) =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) *
        (if a = 1 then 4 * ((k : ℝ) - b) / ((b : ℝ) * (k : ℝ)) else 0) := by
    split_ifs with h
    · subst h
      have hCkb : (k.choose b : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have hE : ((k - 1).choose b : ℝ) =
          (k.choose b : ℝ) * ((k : ℝ) - (b : ℝ)) / (k : ℝ) := by
        rw [eq_div_iff hk0, choose_pred_cast (by omega) (by omega)]
      unfold Coalescent.sfsCladeCoeff
      rw [ite_eq_left (by omega), Nat.choose_one_right, hE]
      field_simp
      ring
    · ring
  have t6 : (if b = 1 then Coalescent.sfsCladeCoeff k a else 0) =
      (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) *
        (if b = 1 then 4 * ((k : ℝ) - a) / ((a : ℝ) * (k : ℝ)) else 0) := by
    split_ifs with h
    · subst h
      unfold Coalescent.sfsCladeCoeff
      rw [ite_eq_left (by omega), Nat.choose_one_right, hsub]
      field_simp
      ring
    · ring
  linear_combination t1 + t2 + t3 - t4 + t5 + t6 +
    (k : ℝ) / (2 * ((k.choose a : ℝ) * ((k - a).choose b : ℝ))) * hW

end Rhone.Statistics
