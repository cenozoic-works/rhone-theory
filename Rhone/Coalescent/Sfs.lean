/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.Kingman

/-!
# Kingman coalescent: expected site frequency spectrum coefficients

Source: fu1995, eq. (14), p. 178, eq. (22), p. 181; wakeley2009, sec. 3.2. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset

def subtendProb (n k i : ℕ) : ℚ := ((n - i - 1).choose (k - 2) : ℚ) / ((n - 1).choose (k - 1))

def expSfsCoeff (n i : ℕ) : ℚ :=
  ∑ k ∈ Icc 2 (n - i + 1), (k : ℚ) * holdingTime k * subtendProb n k i

theorem sum_choose_div_choose {m N : ℕ} (h : m ≤ N) :
    ∑ j ∈ range (m + 1), (m.choose j : ℚ) / (N.choose j) = (N + 1) / (N + 1 - m) := by
  have hCN : (N.choose m : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  have step1 : ∀ j ∈ range (m + 1),
      (m.choose j : ℚ) / (N.choose j) = ((N - j).choose (m - j) : ℚ) / (N.choose m) := by
    intro j hj
    have hj' : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
    have hCj : (N.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hj'.trans h)).ne'
    rw [div_eq_div_iff hCj hCN]
    exact_mod_cast (Nat.choose_mul (n := N) hj').symm.trans (by ring) |>.symm.trans (by ring)
  have step2 : ∑ j ∈ range (m + 1), (N - j).choose (m - j) = (N + 1).choose m := by
    have hr := Finset.sum_range_reflect (fun u => (u + (N - m)).choose (N - m)) (m + 1)
    have h2 := Nat.sum_range_add_choose m (N - m)
    have e : ∀ j ∈ range (m + 1), (N - j).choose (m - j) =
        ((m + 1 - 1 - j) + (N - m)).choose (N - m) := by
      intro j hj
      have hj' : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
      rw [show m + 1 - 1 - j + (N - m) = N - j by omega]
      rw [← Nat.choose_symm (show m - j ≤ N - j by omega), show N - j - (m - j) = N - m by omega]
    rw [Finset.sum_congr rfl e, hr, h2, show m + (N - m) + 1 = N + 1 by omega,
      ← Nat.choose_symm (show N - m + 1 ≤ N + 1 by omega)]
    congr 1
    omega
  rw [Finset.sum_congr rfl step1]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simp_rw [← div_eq_mul_inv]
  have hs : (∑ j ∈ range (m + 1), ((N - j).choose (m - j) : ℚ)) = ((N + 1).choose m : ℚ) := by
    exact_mod_cast step2
  rw [hs]
  have h3 := Nat.choose_mul_succ_eq N m
  have h4 : (N.choose m : ℚ) * (N + 1) = ((N + 1).choose m : ℚ) * (N + 1 - m : ℕ) := by
    exact_mod_cast h3
  have hm : ((N + 1 - m : ℕ) : ℚ) = (N : ℚ) + 1 - m := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hm] at h4
  have hpos : (N : ℚ) + 1 - m ≠ 0 := by
    have : (m : ℚ) ≤ N := by exact_mod_cast h
    linarith
  rw [div_eq_div_iff hCN hpos]
  linarith

theorem term_eq {j m N : ℕ} (hjm : j ≤ m) (hmN : m ≤ N) :
    ((j + 2 : ℕ) : ℚ) * holdingTime (j + 2) *
        (((m.choose j : ℕ) : ℚ) / ((N + 1).choose (j + 1) : ℕ)) =
      2 / (N + 1) * ((m.choose j : ℚ) / (N.choose j)) := by
  have hCN : (N.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hjm.trans hmN)).ne'
  have h1 : ((N : ℚ) + 1) * (N.choose j) = ((N + 1).choose (j + 1) : ℕ) * ((j : ℚ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq N j
  have hj : (j : ℚ) + 1 ≠ 0 := by positivity
  have hN : (N : ℚ) + 1 ≠ 0 := by positivity
  have hC1 : (((N + 1).choose (j + 1) : ℕ) : ℚ) = ((N : ℚ) + 1) * N.choose j / ((j : ℚ) + 1) := by
    rw [eq_div_iff hj, ← h1]
  rw [holdingTime_eq (by omega), hC1]
  push_cast
  have : (j : ℚ) + 2 ≠ 0 := by positivity
  have h2 : (j : ℚ) + 2 - 1 ≠ 0 := by
    intro h; have : (0 : ℚ) ≤ j := Nat.cast_nonneg j; linarith
  field_simp
  ring

theorem expSfsCoeff_eq {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) : expSfsCoeff n i = 2 / i := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, m = N + 2 - i - 1 := ⟨_, rfl⟩
  have hmN : m ≤ N := by omega
  have hrange : Icc 2 (N + 2 - i + 1) = Ico 2 (m + 3) := by
    ext k; simp only [mem_Icc, mem_Ico]; omega
  unfold expSfsCoeff
  rw [hrange, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ j ∈ range (m + 3 - 2),
      ((2 + j : ℕ) : ℚ) * holdingTime (2 + j) * subtendProb (N + 2) (2 + j) i =
        2 / (N + 1) * ((m.choose j : ℚ) / (N.choose j)) := by
    intro j hj
    have hj' : j ≤ m := by simp at hj; omega
    have e1 : subtendProb (N + 2) (2 + j) i =
        ((m.choose j : ℕ) : ℚ) / ((N + 1).choose (j + 1) : ℕ) := by
      unfold subtendProb
      rw [show N + 2 - i - 1 = m by omega, show 2 + j - 2 = j by omega,
        show N + 2 - 1 = N + 1 by omega, show 2 + j - 1 = j + 1 by omega]
    rw [e1, add_comm 2 j]
    exact term_eq hj' hmN
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, show m + 3 - 2 = m + 1 by omega,
    sum_choose_div_choose hmN]
  have hi' : (N : ℚ) + 1 - m = i := by
    have : ((N + 2 - i - 1 : ℕ) : ℚ) = m := by rw [hm]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at this
    push_cast at this
    linarith
  have hN : (N : ℚ) + 1 ≠ 0 := by positivity
  rw [hi']
  field_simp

theorem sum_subtendProb {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Icc 1 (n - k + 1), subtendProb n k i = 1 := by
  have hC : (((n - 1).choose (k - 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k - 1 ≤ n - 1)).ne'
  have hnat : ∑ i ∈ Icc 1 (n - k + 1), (n - i - 1).choose (k - 2) = (n - 1).choose (k - 1) := by
    have h := Nat.sum_Icc_choose (n - 2) (k - 2)
    rw [show n - 2 + 1 = n - 1 by omega, show k - 2 + 1 = k - 1 by omega] at h
    rw [← h]
    refine Finset.sum_nbij' (fun i => n - i - 1) (fun t => n - t - 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [mem_Icc] at hi ⊢; omega
    · intro t ht; simp only [mem_Icc] at ht ⊢; omega
    · intro i hi; simp only [mem_Icc] at hi; omega
    · intro t ht; simp only [mem_Icc] at ht; omega
    · intro i _; rfl
  unfold subtendProb
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hnat, mul_inv_cancel₀ hC]

end Rhone.Coalescent
