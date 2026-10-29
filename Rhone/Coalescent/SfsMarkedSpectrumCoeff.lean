/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Clade occupation coefficient for the Kingman site frequency spectrum

Source: fu1995, eq. 22; kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Coalescent

/-- Source: fu1995, eq. 22. -/
noncomputable def sfsCladeCoeff (k t : ℕ) : ℝ :=
  if t < k then 2 / ((t : ℝ) * (k.choose t : ℝ)) else 0

theorem sfsCladeCoeff_of_le_one {k : ℕ} (hk : k ≤ 1) (t : ℕ) : sfsCladeCoeff k t = 0 := by
  unfold sfsCladeCoeff
  split_ifs with h
  · have ht : t = 0 := by omega
    simp [ht]
  · rfl

/-- Source: fu1995, eq. 22. -/
theorem sfsCladeCoeff_nonneg (k t : ℕ) : 0 ≤ sfsCladeCoeff k t := by
  unfold sfsCladeCoeff
  split_ifs <;> positivity

/-- Source: fu1995, eq. 22. -/
theorem choose_mul_sfsCladeCoeff {k t : ℕ} (ht : 1 ≤ t) (htk : t < k) :
    (k.choose t : ℝ) * sfsCladeCoeff k t = 2 / (t : ℝ) := by
  have hc : (k.choose t : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos htk.le).ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  unfold sfsCladeCoeff
  rw [ite_eq_left htk]
  field_simp

/-- Source: fu1995, eq. 22. -/
theorem sfsCladeCoeff_step {k m : ℕ} (hk : 2 ≤ k) (hm : m ≤ k) :
    (m.choose 2 : ℝ) * sfsCladeCoeff (k - 1) (m - 1) +
        ((k - m).choose 2 : ℝ) * sfsCladeCoeff (k - 1) m =
      (k.choose 2 : ℝ) * sfsCladeCoeff k m - if m = 1 then 1 else 0 := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · simp [sfsCladeCoeff]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [sfsCladeCoeff]
      · have h1 : 1 < j + 2 - 1 := by omega
        have h2 : 1 < j + 2 := by omega
        simp only [sfsCladeCoeff, h1, h2, ite_true, Nat.choose_one_right, Nat.cast_choose_two,
          Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, one_mul]
        rw [show j + 2 - 1 = j + 1 by omega]
        push_cast
        have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
        have hj2 : (j : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
  · rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · have hne : m ≠ 1 := by omega
      simp [sfsCladeCoeff, hne]
    · obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, k = a + d + 3 := ⟨k - a - 3, by omega⟩
      have hne : a + 2 ≠ 1 := by omega
      rw [ite_eq_right hne, sub_zero, show a + d + 3 - 1 = a + d + 2 by omega,
        show a + 2 - 1 = a + 1 by omega, show a + d + 3 - (a + 2) = d + 1 by omega]
      have hx0 : 0 < (a + d + 2).choose (a + 1) := Nat.choose_pos (by omega)
      have hy0 : 0 < (a + d + 2).choose (a + 2) := Nat.choose_pos (by omega)
      have hc0 : 0 < (a + d + 3).choose (a + 2) := Nat.choose_pos (by omega)
      have h1 := Nat.add_one_mul_choose_eq (a + d + 2) (a + 1)
      have h2 := Nat.choose_mul_succ_eq (a + d + 2) (a + 2)
      rw [show a + d + 2 + 1 - (a + 2) = d + 1 by omega] at h2
      have h1R : ((a : ℝ) + d + 3) * ((a + d + 2).choose (a + 1) : ℝ) =
          ((a + d + 3).choose (a + 2) : ℝ) * ((a : ℝ) + 2) := by exact_mod_cast h1
      have h2R : ((a + d + 2).choose (a + 2) : ℝ) * ((a : ℝ) + d + 3) =
          ((a + d + 3).choose (a + 2) : ℝ) * ((d : ℝ) + 1) := by exact_mod_cast h2
      have hK : (a : ℝ) + d + 3 ≠ 0 := by positivity
      have hxE : ((a + d + 2).choose (a + 1) : ℝ) =
          ((a + d + 3).choose (a + 2) : ℝ) * ((a : ℝ) + 2) / ((a : ℝ) + d + 3) := by
        rw [eq_div_iff hK, ← h1R]; ring
      have hyE : ((a + d + 2).choose (a + 2) : ℝ) =
          ((a + d + 3).choose (a + 2) : ℝ) * ((d : ℝ) + 1) / ((a : ℝ) + d + 3) := by
        rw [eq_div_iff hK, ← h2R]
      have hcR : ((a + d + 3).choose (a + 2) : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
      have hsecond : ((d + 1).choose 2 : ℝ) * sfsCladeCoeff (a + d + 2) (a + 2) =
          ((d + 1).choose 2 : ℝ) *
            (2 / (((a + 2 : ℕ) : ℝ) * ((a + d + 2).choose (a + 2) : ℝ))) := by
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · simp
        · rw [sfsCladeCoeff, ite_eq_left (by omega)]
      rw [hsecond, sfsCladeCoeff, ite_eq_left (by omega), sfsCladeCoeff, ite_eq_left (by omega),
        hxE, hyE, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
      push_cast
      have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
      have ha2 : (a : ℝ) + 2 ≠ 0 := by positivity
      have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

end Rhone.Coalescent
