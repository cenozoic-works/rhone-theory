/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Duality
public import Rhone.MarkovChain.CoreBridge
public import Rhone.Coalescent.KingmanChain

/-! # Block-counting duality for the neutral Moran chain -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Matrix MarkovChain Rhone.Combinatorics

theorem one_add_smul_blockChain_Q_apply (N : ℕ) (n m : Fin (N + 1)) :
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) + (2 / (N : ℝ) ^ 2) • (blockChain N).Q) n m =
      (if (m : ℕ) + 1 = n then (n : ℝ) * ((n : ℝ) - 1) / (N : ℝ) ^ 2 else 0) +
      (if m = n then 1 - (n : ℝ) * ((n : ℝ) - 1) / (N : ℝ) ^ 2 else 0) := by
  have hc : (coalRate (n : ℕ) : ℝ) = ((n : ℕ) : ℝ) * (((n : ℕ) : ℝ) - 1) / 2 := by
    simp [coalRate]
  rw [Matrix.add_apply, Matrix.smul_apply, blockChain_Q, blockQ, hc, smul_eq_mul]
  by_cases h2 : m = n
  · subst h2
    have h1 : ¬ ((m : ℕ) + 1 = (m : ℕ)) := by omega
    rw [Matrix.one_apply_eq, ite_eq_right h1, ite_eq_right h1, ite_eq_left rfl,
      ite_eq_left rfl]
    ring
  · rw [Matrix.one_apply_ne (Ne.symm h2), ite_eq_right (c := m = n) h2,
      ite_eq_right (c := m = n) h2]
    by_cases h1 : (m : ℕ) + 1 = (n : ℕ)
    · rw [ite_eq_left h1, ite_eq_left h1]
      ring
    · rw [ite_eq_right h1, ite_eq_right h1]
      ring

noncomputable def moranBlockChain (N : ℕ) : FinChain (Fin (N + 1)) where
  P := 1 + (2 / (N : ℝ) ^ 2) • (blockChain N).Q
  nonneg n m := by
    rw [one_add_smul_blockChain_Q_apply]
    have hn : ((n : ℕ) : ℝ) ≤ N := by exact_mod_cast Fin.is_le n
    have h0 : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc0 : 0 ≤ ((n : ℕ) : ℝ) * (((n : ℕ) : ℝ) - 1) / (N : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos (n : ℕ) with h | h
      · simp [h]
      · have h1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast h
        exact div_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)
    have hc1 : ((n : ℕ) : ℝ) * (((n : ℕ) : ℝ) - 1) / (N : ℝ) ^ 2 ≤ 1 :=
      div_le_one_of_le₀ (by nlinarith) (sq_nonneg _)
    split_ifs <;> linarith
  row_sum n := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      (blockChain N).row_sum n, mul_zero, add_zero, Matrix.one_apply, sum_ite_eq, mem_univ,
      ite_true]

noncomputable def hypergeomDual (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i n => ((i : ℕ).choose n : ℝ) / (N.choose n : ℝ)

theorem moranBlockChain_apply (N : ℕ) (n m : Fin (N + 1)) :
    (moranBlockChain N).P n m =
      (if (m : ℕ) + 1 = n then (n : ℝ) * ((n : ℝ) - 1) / (N : ℝ) ^ 2 else 0) +
      (if m = n then 1 - (n : ℝ) * ((n : ℝ) - 1) / (N : ℝ) ^ 2 else 0) :=
  one_add_smul_blockChain_Q_apply N n m

theorem sum_moranBlockChain_mul (N : ℕ) (u : ℕ → ℝ) (n : Fin (N + 1)) :
    ∑ m, (moranBlockChain N).P n m * u m =
      u n + ((n : ℕ) : ℝ) * (((n : ℕ) : ℝ) - 1) / (N : ℝ) ^ 2 * (u ((n : ℕ) - 1) - u n) := by
  simp only [moranBlockChain_apply, add_mul, ite_mul, zero_mul, sum_add_distrib,
    Finset.sum_ite_eq', mem_univ, ite_true]
  have hsum : ∑ m : Fin (N + 1), (if (m : ℕ) + 1 = (n : ℕ) then
      ((n : ℕ) : ℝ) * (((n : ℕ) : ℝ) - 1) / (N : ℝ) ^ 2 * u m else 0) =
      ((n : ℕ) : ℝ) * (((n : ℕ) : ℝ) - 1) / (N : ℝ) ^ 2 * u ((n : ℕ) - 1) := by
    rcases Nat.eq_zero_or_pos (n : ℕ) with h | h
    · rw [h]
      simp
    · rw [Finset.sum_eq_single (⟨(n : ℕ) - 1, by omega⟩ : Fin (N + 1))]
      · rw [ite_eq_left (by simp only; omega)]
      · intro m _ hm
        refine ite_eq_right fun h' => hm (Fin.ext ?_)
        simp only
        omega
      · intro h'
        exact absurd (mem_univ _) h'
  rw [hsum]
  ring

theorem hypergeom_moran_step {N n : ℕ} (i : ℕ) (hn : n ≤ N) :
    (i.choose n : ℝ) / (N.choose n : ℝ)
        + (i : ℝ) * ((N : ℝ) - i) / (N : ℝ) ^ 2 *
          (((i + 1).choose n : ℝ) / (N.choose n : ℝ) - (i.choose n : ℝ) / (N.choose n : ℝ))
        + (i : ℝ) * ((N : ℝ) - i) / (N : ℝ) ^ 2 *
          (((i - 1).choose n : ℝ) / (N.choose n : ℝ) - (i.choose n : ℝ) / (N.choose n : ℝ)) =
      (i.choose n : ℝ) / (N.choose n : ℝ)
        + (n : ℝ) * ((n : ℝ) - 1) / (N : ℝ) ^ 2 *
          ((i.choose (n - 1) : ℝ) / (N.choose (n - 1) : ℝ)
            - (i.choose n : ℝ) / (N.choose n : ℝ)) := by
  rcases i with _ | j
  · rcases n with _ | _ | k
    · simp
    · simp
    · simp
  rcases n with _ | _ | k
  · simp
  · simp only [zero_add, Nat.choose_one_right, Nat.add_sub_cancel, Nat.sub_self,
      Nat.choose_zero_right, Nat.cast_one, div_one]
    push_cast
    ring
  · have hk1 : k + 1 + 1 - 1 = k + 1 := rfl
    have hj1 : j + 1 - 1 = j := rfl
    rw [hk1, hj1]
    have hY0 : (N.choose (k + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have hNk : (N : ℝ) - k - 1 ≠ 0 := by
      have h : ((k + 1 + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
      push_cast at h
      intro h'
      linarith
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hD : (N.choose (k + 1 + 1) : ℝ) =
        ((N : ℝ) - k - 1) * (N.choose (k + 1) : ℝ) / ((k : ℝ) + 2) := by
      have h := Nat.choose_succ_right_eq N (k + 1)
      have h' : (N.choose (k + 1 + 1) : ℝ) * ((k : ℝ) + 2) =
          (N.choose (k + 1) : ℝ) * ((N : ℝ) - k - 1) := by
        have hc := congrArg (Nat.cast : ℕ → ℝ) h
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at hc
        push_cast at hc
        linarith
      field_simp
      linarith
    have h1 : ((j + 1 + 1).choose (k + 1 + 1) : ℝ) =
        ((j + 1).choose (k + 1) : ℝ) + ((j + 1).choose (k + 1 + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (j + 1) (k + 1)
    have h2 : (j.choose (k + 1 + 1) : ℝ) =
        ((j + 1).choose (k + 1 + 1) : ℝ) - (j.choose (k + 1) : ℝ) := by
      have h : ((j + 1).choose (k + 1 + 1) : ℝ) =
          (j.choose (k + 1) : ℝ) + (j.choose (k + 1 + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ j (k + 1)
      linarith
    have h3 : (j.choose (k + 1) : ℝ) =
        ((j + 1).choose (k + 1) : ℝ) - (j.choose k : ℝ) := by
      have h : ((j + 1).choose (k + 1) : ℝ) = (j.choose k : ℝ) + (j.choose (k + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ j k
      linarith
    have hB : (j.choose k : ℝ) =
        ((k : ℝ) + 1) * ((j + 1).choose (k + 1) : ℝ) / ((j : ℝ) + 1) := by
      have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq j k)
      push_cast at h
      field_simp
      linarith
    have hC : ((j + 1).choose (k + 1 + 1) : ℝ) =
        ((j : ℝ) - k) * ((j + 1).choose (k + 1) : ℝ) / ((k : ℝ) + 2) := by
      rcases Nat.lt_or_ge j k with hjk | hjk
      · rw [Nat.choose_eq_zero_of_lt (by omega : j + 1 < k + 1 + 1),
          Nat.choose_eq_zero_of_lt (by omega : j + 1 < k + 1)]
        simp
      · have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq (j + 1) (k + 1))
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at h
        push_cast at h
        field_simp
        linarith
    rw [h1, h2, h3, hB, hC, hD]
    push_cast
    field_simp
    ring

/-- Source: mohle1999, Thm 3.1, p. 766, eq. (10), p. 769. -/
theorem moran_blockCount_duality (N : ℕ) :
    FinChain.MomentDuality (moranChain N 1 one_pos) (moranBlockChain N) (hypergeomDual N) := by
  refine FinChain.MomentDuality.of_step ?_
  ext i n
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ j, (moranChain N 1 one_pos).P i j * hypergeomDual N j n = _ :=
    moran_expect (N := N) (r := 1)
      (fun k : ℕ => (k.choose (n : ℕ) : ℝ) / (N.choose (n : ℕ) : ℝ)) i
  have hR : ∑ m, hypergeomDual N i m * (moranBlockChain N).Pᵀ m n = _ :=
    (Finset.sum_congr rfl fun m _ => by
      rw [Matrix.transpose_apply, mul_comm]
      rfl).trans
      (sum_moranBlockChain_mul N (fun k : ℕ => ((i : ℕ).choose k : ℝ) / (N.choose k : ℝ)) n)
  refine (hL.trans ?_).trans hR.symm
  rw [moranUp_one, moranDown_one]
  exact hypergeom_moran_step (i : ℕ) (Fin.is_le n)

end Rhone.Coalescent
